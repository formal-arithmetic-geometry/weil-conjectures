/- Representation matrix for the historical cone declaration. -/

-- D0: Cone (quotPowFunctor J I ⋙ tensorLeft K)
-- D1: Cone (namedAbbrev J I K)
-- D2: Cone (namedDef J I K)
-- D3: Cone (namedReducible J I K)
-- D4: Cone ((namedDef J I K).unfolded body)

-- Instance dimension:
-- I0: inferred concrete MonoidalCategory (DerivedCategory ...)
-- I1: explicit/shared local MonoidalCategory parameter

-- Measured 2x2: B00 >600 s, B10 ~17 s, B01 18 s, B11 5.3 s API / 9.5 s real term.
