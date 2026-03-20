LaborForceScheduler Logo Assets

Place logo files in this folder using these exact filenames:

1) header_logo.png
   - Used in the app header (small).
   - Recommended: transparent PNG, roughly square, at least 128x128.

2) store_logo.png
   - Preferred for Store-tab branding (larger).
   - Recommended: transparent PNG, landscape-friendly, at least 800x300.

Fallback order:
- Header branding: header_logo.png -> legacy header_logo.png -> legacy petroserve.png.
- Store-tab branding: store_logo.png -> header_logo.png -> legacy petroserve.png.
- When Pillow is unavailable, both header and Store tab still try tkinter PhotoImage loading.

Notes:
- If files are missing, the app safely falls back to legacy assets or text fallback branding.
- Keep file sizes reasonable (under ~2 MB each) for fast startup.
