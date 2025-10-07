"""
Finite-Size Scaling Analysis for Spatial Dimension Convergence

Fits various scaling ansätze to the multi-method consensus dimension data:
- d(N) = d_∞ - a/N^b (power law with free exponent)
- d(N) = d_∞ - a/N (linear finite-size correction)
- d(N) = d_∞ - a/N - b/N^2 (polynomial expansion)

Extrapolates to N→∞ limit and computes confidence intervals.

Session 4 Sprint 9 Phase 3
Expert recommendation: Develop Coxeter-based scaling theory

Date: October 7, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from scipy.stats import t as student_t
import json
from datetime import datetime

# ==============================================================================
# Data from Multi-Method Analysis (Session 4 Phase 2)
# ==============================================================================

# Consensus dimension data from N=4-7
N_values = np.array([4, 5, 6, 7])
d_consensus = np.array([1.24, 1.77, 1.87, 2.07])
d_std = np.array([1.38, 0.94, 0.69, 0.68])

# Individual method data for comparison
d_correlation = np.array([3.16, 2.38, 2.69, 2.98])
d_persistent_homology = np.array([0.00, 0.44, 1.00, 1.37])
d_graph_theoretic = np.array([0.57, 2.49, 1.92, 1.86])

# ==============================================================================
# Scaling Model Functions
# ==============================================================================

def model_power_law(N, d_inf, a, b):
    """
    Power law: d(N) = d_inf - a/N^b

    Most general finite-size scaling form.
    - d_inf: continuum limit dimension
    - a: amplitude of finite-size correction
    - b: exponent (determines convergence rate)
    """
    return d_inf - a / (N ** b)

def model_linear(N, d_inf, a):
    """
    Linear: d(N) = d_inf - a/N

    Simplest finite-size scaling (b=1 case).
    """
    return d_inf - a / N

def model_quadratic(N, d_inf, a, b_coef):
    """
    Quadratic: d(N) = d_inf - a/N - b/N^2

    Polynomial expansion for stronger finite-size effects.
    """
    return d_inf - a / N - b_coef / (N**2)

def model_exponential(N, d_inf, a, b):
    """
    Exponential: d(N) = d_inf - a * exp(-b*N)

    Alternative convergence form.
    """
    return d_inf - a * np.exp(-b * N)

# ==============================================================================
# Fitting Functions
# ==============================================================================

def fit_model(model, N_data, d_data, d_errors, bounds, p0=None):
    """
    Fit a scaling model to dimension data.

    Args:
        model: Function d(N, *params)
        N_data: Array of N values
        d_data: Array of dimension values
        d_errors: Array of dimension uncertainties
        bounds: Tuple of (lower_bounds, upper_bounds) for parameters
        p0: Initial parameter guesses

    Returns:
        dict with fit results and diagnostics
    """
    try:
        # Fit with uncertainty weighting
        popt, pcov = curve_fit(
            model, N_data, d_data,
            sigma=d_errors,
            absolute_sigma=True,
            bounds=bounds,
            p0=p0,
            maxfev=10000
        )

        # Compute residuals and chi-squared
        d_pred = model(N_data, *popt)
        residuals = d_data - d_pred
        chi2 = np.sum((residuals / d_errors)**2)
        dof = len(N_data) - len(popt)
        chi2_reduced = chi2 / dof if dof > 0 else np.inf

        # Compute R-squared
        ss_res = np.sum(residuals**2)
        ss_tot = np.sum((d_data - np.mean(d_data))**2)
        r_squared = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0.0

        # Parameter uncertainties (1-sigma)
        perr = np.sqrt(np.diag(pcov))

        # Compute confidence intervals for d_inf (first parameter)
        # 95% confidence interval using Student's t-distribution
        alpha = 0.05
        t_val = student_t.ppf(1 - alpha/2, dof) if dof > 0 else np.inf
        d_inf_95ci = t_val * perr[0]

        return {
            'success': True,
            'params': popt,
            'param_errors': perr,
            'covariance': pcov,
            'd_inf': popt[0],
            'd_inf_error': perr[0],
            'd_inf_95ci': d_inf_95ci,
            'chi2': chi2,
            'chi2_reduced': chi2_reduced,
            'r_squared': r_squared,
            'residuals': residuals,
            'dof': dof
        }
    except Exception as e:
        return {
            'success': False,
            'error': str(e)
        }

# ==============================================================================
# Main Analysis
# ==============================================================================

def analyze_scaling():
    """
    Fit all scaling models to consensus dimension data.
    """
    print("=" * 80)
    print("FINITE-SIZE SCALING ANALYSIS")
    print("=" * 80)
    print()
    print("Data: N=4,5,6,7 consensus dimension from 3 methods")
    print("Goal: Extrapolate to N->inf continuum limit")
    print()
    print("-" * 80)
    print(f"{'N':<5} {'d_consensus':<12} {'std':<8}")
    print("-" * 80)
    for i, N in enumerate(N_values):
        print(f"{N:<5} {d_consensus[i]:<12.3f} {d_std[i]:<8.3f}")
    print("-" * 80)
    print()

    results = {}

    # Model 1: Power Law d(N) = d_inf - a/N^b
    print("MODEL 1: Power Law d(N) = d_inf - a/N^b")
    print("-" * 80)
    result_power = fit_model(
        model_power_law, N_values, d_consensus, d_std,
        bounds=([2.0, 0.0, 0.1], [4.0, 20.0, 3.0]),  # d_inf in [2,4], a in [0,20], b in [0.1,3]
        p0=[3.0, 5.0, 1.0]
    )
    if result_power['success']:
        d_inf, a, b = result_power['params']
        print(f"  d_inf = {d_inf:.3f} +/- {result_power['d_inf_error']:.3f}")
        print(f"  95% CI: [{d_inf - result_power['d_inf_95ci']:.3f}, {d_inf + result_power['d_inf_95ci']:.3f}]")
        print(f"  a = {a:.3f} +/- {result_power['param_errors'][1]:.3f}")
        print(f"  b = {b:.3f} +/- {result_power['param_errors'][2]:.3f}")
        print(f"  chi2/dof = {result_power['chi2_reduced']:.3f}")
        print(f"  R2 = {result_power['r_squared']:.4f}")
        results['power_law'] = result_power
    else:
        print(f"  FAILED: {result_power['error']}")
    print()

    # Model 2: Linear d(N) = d_inf - a/N
    print("MODEL 2: Linear d(N) = d_inf - a/N")
    print("-" * 80)
    result_linear = fit_model(
        model_linear, N_values, d_consensus, d_std,
        bounds=([2.0, 0.0], [4.0, 20.0]),
        p0=[3.0, 5.0]
    )
    if result_linear['success']:
        d_inf, a = result_linear['params']
        print(f"  d_inf = {d_inf:.3f} +/- {result_linear['d_inf_error']:.3f}")
        print(f"  95% CI: [{d_inf - result_linear['d_inf_95ci']:.3f}, {d_inf + result_linear['d_inf_95ci']:.3f}]")
        print(f"  a = {a:.3f} +/- {result_linear['param_errors'][1]:.3f}")
        print(f"  chi2/dof = {result_linear['chi2_reduced']:.3f}")
        print(f"  R2 = {result_linear['r_squared']:.4f}")
        results['linear'] = result_linear
    else:
        print(f"  FAILED: {result_linear['error']}")
    print()

    # Model 3: Quadratic d(N) = d_inf - a/N - b/N^2
    print("MODEL 3: Quadratic d(N) = d_inf - a/N - b/N^2")
    print("-" * 80)
    result_quad = fit_model(
        model_quadratic, N_values, d_consensus, d_std,
        bounds=([2.0, -10.0, -10.0], [4.0, 20.0, 20.0]),
        p0=[3.0, 5.0, 0.0]
    )
    if result_quad['success']:
        d_inf, a, b_coef = result_quad['params']
        print(f"  d_inf = {d_inf:.3f} +/- {result_quad['d_inf_error']:.3f}")
        print(f"  95% CI: [{d_inf - result_quad['d_inf_95ci']:.3f}, {d_inf + result_quad['d_inf_95ci']:.3f}]")
        print(f"  a = {a:.3f} +/- {result_quad['param_errors'][1]:.3f}")
        print(f"  b = {b_coef:.3f} +/- {result_quad['param_errors'][2]:.3f}")
        print(f"  chi2/dof = {result_quad['chi2_reduced']:.3f}")
        print(f"  R2 = {result_quad['r_squared']:.4f}")
        results['quadratic'] = result_quad
    else:
        print(f"  FAILED: {result_quad['error']}")
    print()

    # Model 4: Exponential d(N) = d_inf - a*exp(-b*N)
    print("MODEL 4: Exponential d(N) = d_inf - a*exp(-b*N)")
    print("-" * 80)
    result_exp = fit_model(
        model_exponential, N_values, d_consensus, d_std,
        bounds=([2.0, 0.0, 0.0], [4.0, 10.0, 2.0]),
        p0=[3.0, 2.0, 0.5]
    )
    if result_exp['success']:
        d_inf, a, b = result_exp['params']
        print(f"  d_inf = {d_inf:.3f} +/- {result_exp['d_inf_error']:.3f}")
        print(f"  95% CI: [{d_inf - result_exp['d_inf_95ci']:.3f}, {d_inf + result_exp['d_inf_95ci']:.3f}]")
        print(f"  a = {a:.3f} +/- {result_exp['param_errors'][1]:.3f}")
        print(f"  b = {b:.3f} +/- {result_exp['param_errors'][2]:.3f}")
        print(f"  chi2/dof = {result_exp['chi2_reduced']:.3f}")
        print(f"  R2 = {result_exp['r_squared']:.4f}")
        results['exponential'] = result_exp
    else:
        print(f"  FAILED: {result_exp['error']}")
    print()

    return results

# ==============================================================================
# Visualization
# ==============================================================================

def plot_scaling_fits(results):
    """
    Create comprehensive visualization of scaling fits.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.suptitle('Finite-Size Scaling Analysis: Dimension Convergence to N->inf',
                 fontsize=16, fontweight='bold')

    # Extended N range for extrapolation
    N_extended = np.linspace(4, 15, 200)

    # Color scheme
    colors = {
        'power_law': '#e74c3c',
        'linear': '#3498db',
        'quadratic': '#2ecc71',
        'exponential': '#9b59b6'
    }

    model_names = {
        'power_law': 'Power Law: d_inf - a/N^b',
        'linear': 'Linear: d_inf - a/N',
        'quadratic': 'Quadratic: d_inf - a/N - b/N^2',
        'exponential': 'Exponential: d_inf - a*exp(-bN)'
    }

    # Plot 1: All fits together
    ax = axes[0, 0]
    ax.errorbar(N_values, d_consensus, yerr=d_std, fmt='ko', markersize=8,
                capsize=5, capthick=2, label='Data (consensus)', zorder=5)

    for model_key, result in results.items():
        if result['success']:
            if model_key == 'power_law':
                d_fit = model_power_law(N_extended, *result['params'])
            elif model_key == 'linear':
                d_fit = model_linear(N_extended, *result['params'])
            elif model_key == 'quadratic':
                d_fit = model_quadratic(N_extended, *result['params'])
            elif model_key == 'exponential':
                d_fit = model_exponential(N_extended, *result['params'])

            d_inf = result['d_inf']
            ci = result['d_inf_95ci']
            label = f"{model_names[model_key]}\nd_inf={d_inf:.2f}+/-{ci:.2f}"
            ax.plot(N_extended, d_fit, color=colors[model_key], linewidth=2,
                   alpha=0.8, label=label)
            ax.axhline(d_inf, color=colors[model_key], linestyle='--', alpha=0.3)

    ax.axhline(3.0, color='black', linestyle=':', linewidth=2, label='Target d=3', zorder=1)
    ax.set_xlabel('N (number of elements)', fontsize=12)
    ax.set_ylabel('Spatial Dimension d', fontsize=12)
    ax.set_title('All Scaling Models', fontsize=13, fontweight='bold')
    ax.legend(fontsize=9, loc='lower right')
    ax.grid(True, alpha=0.3)
    ax.set_xlim(3.5, 15)
    ax.set_ylim(1.0, 3.5)

    # Plot 2: Residuals
    ax = axes[0, 1]
    for model_key, result in results.items():
        if result['success']:
            ax.plot(N_values, result['residuals'], 'o-', color=colors[model_key],
                   markersize=8, linewidth=2, label=model_names[model_key].split(':')[0])
    ax.axhline(0, color='black', linestyle='--', linewidth=1)
    ax.set_xlabel('N', fontsize=12)
    ax.set_ylabel('Residuals (data - fit)', fontsize=12)
    ax.set_title('Fit Residuals', fontsize=13, fontweight='bold')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    # Plot 3: Comparison table
    ax = axes[1, 0]
    ax.axis('off')

    table_data = [['Model', 'd_inf', '95% CI', 'chi2/dof', 'R2']]
    for model_key, result in results.items():
        if result['success']:
            d_inf = result['d_inf']
            ci = result['d_inf_95ci']
            chi2 = result['chi2_reduced']
            r2 = result['r_squared']
            model_name = model_names[model_key].split(':')[0]
            table_data.append([
                model_name,
                f"{d_inf:.3f}",
                f"+/-{ci:.3f}",
                f"{chi2:.3f}",
                f"{r2:.4f}"
            ])

    table = ax.table(cellText=table_data, cellLoc='center', loc='center',
                     colWidths=[0.25, 0.15, 0.15, 0.15, 0.15])
    table.auto_set_font_size(False)
    table.set_fontsize(10)
    table.scale(1, 2)

    # Header formatting
    for i in range(5):
        table[(0, i)].set_facecolor('#34495e')
        table[(0, i)].set_text_props(weight='bold', color='white')

    ax.set_title('Model Comparison', fontsize=13, fontweight='bold', pad=20)

    # Plot 4: Best fit with confidence band
    ax = axes[1, 1]

    # Find best model (highest R²)
    best_model = max(results.items(), key=lambda x: x[1]['r_squared'] if x[1]['success'] else -1)
    model_key, result = best_model

    ax.errorbar(N_values, d_consensus, yerr=d_std, fmt='ko', markersize=10,
                capsize=5, capthick=2, label='Data', zorder=5)

    if model_key == 'power_law':
        d_fit = model_power_law(N_extended, *result['params'])
    elif model_key == 'linear':
        d_fit = model_linear(N_extended, *result['params'])
    elif model_key == 'quadratic':
        d_fit = model_quadratic(N_extended, *result['params'])
    elif model_key == 'exponential':
        d_fit = model_exponential(N_extended, *result['params'])

    ax.plot(N_extended, d_fit, color=colors[model_key], linewidth=3,
           label=f"Best Fit: {model_names[model_key].split(':')[0]}")

    d_inf = result['d_inf']
    ci = result['d_inf_95ci']
    ax.axhline(d_inf, color=colors[model_key], linestyle='--', linewidth=2,
              label=f"d_inf = {d_inf:.2f} +/- {ci:.2f} (95% CI)")
    ax.axhspan(d_inf - ci, d_inf + ci, color=colors[model_key], alpha=0.2)
    ax.axhline(3.0, color='black', linestyle=':', linewidth=2, label='Target d=3')

    ax.set_xlabel('N (number of elements)', fontsize=12)
    ax.set_ylabel('Spatial Dimension d', fontsize=12)
    ax.set_title(f'Best Fit (R²={result["r_squared"]:.4f})',
                fontsize=13, fontweight='bold')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xlim(3.5, 15)
    ax.set_ylim(1.0, 3.5)

    plt.tight_layout()

    # Save figure
    output_dir = 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/paper/supporting_material/spacetime_research'
    plt.savefig(f'{output_dir}/scaling_fits.png', dpi=300, bbox_inches='tight')
    plt.savefig(f'{output_dir}/scaling_fits.svg', bbox_inches='tight')
    print(f"[OK] Figures saved to {output_dir}/scaling_fits.png/svg")

    # plt.show()  # Disabled for non-interactive execution
    plt.close()

# ==============================================================================
# Save Results
# ==============================================================================

def save_results(results):
    """
    Save fit results to JSON.
    """
    output_dir = 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/paper/supporting_material/spacetime_research'

    # Convert to serializable format
    serializable = {
        'metadata': {
            'date': datetime.now().isoformat(),
            'data_source': 'Session 4 Phase 2 multi-method consensus',
            'N_values': N_values.tolist(),
            'd_consensus': d_consensus.tolist(),
            'd_std': d_std.tolist()
        },
        'fits': {}
    }

    for model_key, result in results.items():
        if result['success']:
            serializable['fits'][model_key] = {
                'params': result['params'].tolist(),
                'param_errors': result['param_errors'].tolist(),
                'd_inf': float(result['d_inf']),
                'd_inf_error': float(result['d_inf_error']),
                'd_inf_95ci': float(result['d_inf_95ci']),
                'chi2': float(result['chi2']),
                'chi2_reduced': float(result['chi2_reduced']),
                'r_squared': float(result['r_squared']),
                'residuals': result['residuals'].tolist(),
                'dof': int(result['dof'])
            }

    output_file = f'{output_dir}/scaling_fits.json'
    with open(output_file, 'w') as f:
        json.dump(serializable, f, indent=2)

    print(f"[OK] Results saved to {output_file}")

# ==============================================================================
# Main Execution
# ==============================================================================

def main():
    """
    Run complete scaling analysis.
    """
    # Fit all models
    results = analyze_scaling()

    # Summary
    print("=" * 80)
    print("SUMMARY: CONTINUUM LIMIT ESTIMATES")
    print("=" * 80)
    print()

    successful_fits = {k: v for k, v in results.items() if v['success']}

    if successful_fits:
        # Find best fit
        best_model = max(successful_fits.items(), key=lambda x: x[1]['r_squared'])
        best_key, best_result = best_model

        print(f"Best Fit: {best_key.replace('_', ' ').title()}")
        print(f"  d_inf = {best_result['d_inf']:.3f} +/- {best_result['d_inf_error']:.3f}")
        print(f"  95% CI: [{best_result['d_inf'] - best_result['d_inf_95ci']:.3f}, "
              f"{best_result['d_inf'] + best_result['d_inf_95ci']:.3f}]")
        print(f"  R2 = {best_result['r_squared']:.4f}")
        print()

        # Check if consistent with d=3
        d_inf = best_result['d_inf']
        ci = best_result['d_inf_95ci']
        if d_inf - ci <= 3.0 <= d_inf + ci:
            print("[OK] Result CONSISTENT with d=3 at 95% confidence level")
        else:
            print(f"[WARN] Result {abs(d_inf - 3.0)/ci:.2f} sigma from d=3")
        print()

        # All estimates
        print("All Model Estimates:")
        for model_key in ['power_law', 'linear', 'quadratic', 'exponential']:
            if model_key in successful_fits:
                result = successful_fits[model_key]
                print(f"  {model_key.replace('_', ' ').title():<15}: "
                      f"{result['d_inf']:.3f} +/- {result['d_inf_95ci']:.3f}")
        print()

        # Consensus across models
        d_inf_values = [r['d_inf'] for r in successful_fits.values()]
        d_inf_mean = np.mean(d_inf_values)
        d_inf_std = np.std(d_inf_values)
        print(f"Model Consensus: d_inf = {d_inf_mean:.3f} +/- {d_inf_std:.3f}")
        print()

    # Create visualizations
    plot_scaling_fits(results)

    # Save results
    save_results(results)

    print("=" * 80)
    print("ANALYSIS COMPLETE")
    print("=" * 80)

if __name__ == '__main__':
    main()
