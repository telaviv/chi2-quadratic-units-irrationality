"""Mechanical mz-generalisation helper for Chi2U/NonVan/* (stage B2, lemmaP_m)."""
import sys
REPL = [("Q5", "Qd mz"), ("Bfun 2 ", "Bfun mz "), ("Afun 2 ", "Afun mz "), ("Psum 2 ", "Psum mz "),
        ("muPoly 2 ", "muPoly mz "), ("zK 2", "zK mz"), ("Fl ℓ", "Fl mz ℓ"), ("zb ℓ", "zb mz ℓ"),
        ("Rl ℓ", "Rl mz ℓ"), ("red ℓ", "red mz ℓ"), ("GramF 2 ", "GramF mz "), ("Delta 2 ", "Delta mz "),
        ("(mz := 2)", "(mz := mz)"), ("Lmom 2 ", "Lmom mz "),
        ("eB ℓ", "eB mz ℓ"), ("cB ℓ", "cB mz ℓ"), ("dB ℓ", "dB mz ℓ"), ("Bmat ℓ", "Bmat mz ℓ"),
        ("(4 * zb mz ℓ)", "(((2 * mz : ℕ) : Fl mz ℓ) * zb mz ℓ)")]
for p in sys.argv[1:]:
    s = open(p, encoding='utf-8').read()
    for a, b in REPL:
        s = s.replace(a, b)
    open(p, 'w', encoding='utf-8').write(s)
