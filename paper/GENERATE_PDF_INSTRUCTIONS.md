# Generate PDF for Logic Field Theory Paper

## Method 1: Browser (Easiest - Recommended)

1. **Open the HTML file**:
   - Navigate to `paper/Logic_Field_Theory_Logic_Realism.html`
   - Double-click to open in your default browser

2. **Print to PDF**:
   - Press `Ctrl+P` (Windows/Linux) or `Cmd+P` (Mac)
   - Select "Save as PDF" or "Microsoft Print to PDF" as printer
   - **Recommended settings**:
     - Layout: Portrait
     - Margins: Default
     - Background graphics: ON (to preserve styling)
     - Headers and footers: OFF
   - Click "Save" or "Print"
   - Save as: `Logic_Field_Theory_Logic_Realism.pdf`

**Result**: High-quality PDF with table of contents, formatting, and styling preserved

## Method 2: Pandoc with LaTeX (If LaTeX installed)

```bash
cd paper
pandoc Logic_Realism_Foundational_Paper.md -o Logic_Field_Theory_Logic_Realism.pdf \
  --pdf-engine=pdflatex \
  --variable=geometry:margin=1in \
  --variable=documentclass:article \
  --variable=fontsize:11pt \
  --variable=colorlinks:true \
  --table-of-contents \
  --number-sections
```

**Requirements**:
- Pandoc (already installed at `/c/Program Files/Pandoc/pandoc`)
- LaTeX distribution (MiKTeX or TeX Live) - **Not currently installed**

To install MiKTeX: https://miktex.org/download

## Method 3: Online Conversion

1. Upload `Logic_Realism_Foundational_Paper.md` to https://www.markdowntopdf.com/
2. Download the generated PDF
3. Save as `Logic_Field_Theory_Logic_Realism.pdf`

---

**Recommended**: Use Method 1 (Browser) - it's fastest and preserves all formatting from the HTML version.
