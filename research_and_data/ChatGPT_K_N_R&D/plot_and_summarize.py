#!/usr/bin/env python3
"""Read giant-component and spectral-sweep CSVs, plot per-N curves, and print a short summary.
Saves plots to the provided plot directory.
"""
import argparse
import csv
import os
import math

def read_giant(path):
    data = {}
    with open(path, newline='') as f:
        r = csv.DictReader(f)
        for row in r:
            N = int(row['N']); K = int(row['K'])
            size = int(row['|V_K|'])
            frac = float(row['largest_fraction'])
            data.setdefault(N, {})[K] = (size, frac)
    return data

def read_spectral(path):
    data = {}
    with open(path, newline='') as f:
        r = csv.DictReader(f)
        for row in r:
            N = int(row['N']); K = int(row['K'])
            size = int(row['|V_K|'])
            gap = float(row['spectral_gap'])
            data.setdefault(N, {})[K] = (size, gap)
    return data

def ensure(d):
    os.makedirs(d, exist_ok=True)

def plot_and_save(N, ks, fracs, gaps, outpath):
    try:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
    except Exception as e:
        print('matplotlib missing, skipping plots for N=', N)
        return
    fig, ax1 = plt.subplots(figsize=(6,3))
    ax1.plot(ks, fracs, marker='o', color='C0', label='largest fraction')
    ax1.set_xlabel('K')
    ax1.set_ylabel('largest fraction', color='C0')
    ax1.tick_params(axis='y', labelcolor='C0')
    ax2 = ax1.twinx()
    ax2.plot(ks, gaps, marker='x', color='C1', label='spectral gap')
    ax2.set_ylabel('spectral gap', color='C1')
    ax2.tick_params(axis='y', labelcolor='C1')
    plt.title(f'N={N} giant fraction & spectral gap')
    fig.tight_layout()
    fig.savefig(outpath)
    plt.close(fig)

def summarize(N, giant_data, spectral_data):
    ks = sorted(set(list(giant_data.keys()) + list(spectral_data.keys())))
    fracs = [giant_data.get(k,(0,0.0))[1] for k in ks]
    gaps = [spectral_data.get(k,(0,0.0))[1] for k in ks]
    # candidate K
    Kcand = max(0, N-2)
    cand_frac = giant_data.get(Kcand, (0,0.0))[1]
    cand_gap = spectral_data.get(Kcand, (0,0.0))[1]
    # find K with max jump in fraction (delta frac)
    delta_fracs = [fracs[i]-fracs[i-1] if i>0 else fracs[0] for i in range(len(fracs))]
    max_jump_idx = max(range(len(delta_fracs)), key=lambda i: delta_fracs[i])
    K_jump = ks[max_jump_idx]
    jump_val = delta_fracs[max_jump_idx]
    # find K with max increase in spectral gap (delta gap)
    delta_gaps = [gaps[i]-gaps[i-1] if i>0 else gaps[0] for i in range(len(gaps))]
    max_gap_idx = max(range(len(delta_gaps)), key=lambda i: delta_gaps[i])
    K_gap_jump = ks[max_gap_idx]
    gap_jump_val = delta_gaps[max_gap_idx]
    # find K with max gap value
    max_gap_idx2 = max(range(len(gaps)), key=lambda i: gaps[i])
    K_gap_max = ks[max_gap_idx2]
    gap_max_val = gaps[max_gap_idx2]

    verdict = {
        'N': N,
        'K_candidate': Kcand,
        'candidate_fraction': cand_frac,
        'candidate_gap': cand_gap,
        'K_jump_fraction': K_jump,
        'jump_value_fraction': jump_val,
        'K_gap_jump': K_gap_jump,
        'gap_jump_value': gap_jump_val,
        'K_gap_max': K_gap_max,
        'gap_max_value': gap_max_val,
    }
    return ks, fracs, gaps, verdict

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--giant-csv', default='ChatGPT_K_N_R&D/giant_component_curve_N_3_8.csv')
    parser.add_argument('--spectral-csv', default='ChatGPT_K_N_R&D/spectral_sweep_N_3_8.csv')
    parser.add_argument('--plot-dir', default='ChatGPT_K_N_R&D/plots')
    args = parser.parse_args()
    giant = read_giant(args.giant_csv)
    spectral = read_spectral(args.spectral_csv)
    ensure(args.plot_dir)
    all_verdicts = []
    Ns = sorted(set(list(giant.keys()) + list(spectral.keys())))
    for N in Ns:
        ks, fracs, gaps, verdict = summarize(N, giant.get(N, {}), spectral.get(N, {}))
        plot_path = os.path.join(args.plot_dir, f'summary_N_{N}.png')
        plot_and_save(N, ks, fracs, gaps, plot_path)
        all_verdicts.append(verdict)
    # print compact summary
    print('\nPer-N summary (candidate K = N-2):')
    for v in all_verdicts:
        print(f"N={v['N']}: K_candidate={v['K_candidate']}, fraction={v['candidate_fraction']:.4f}, gap={v['candidate_gap']:.6f}")
        print(f"  largest fractional jump at K={v['K_jump_fraction']} (Δfrac={v['jump_value_fraction']:.4f})")
        print(f"  largest spectral-gap jump at K={v['K_gap_jump']} (Δgap={v['gap_jump_value']:.6f}), max gap at K={v['K_gap_max']} (gap={v['gap_max_value']:.6f})")
    print('\nPlots saved to', args.plot_dir)

if __name__ == '__main__':
    main()
