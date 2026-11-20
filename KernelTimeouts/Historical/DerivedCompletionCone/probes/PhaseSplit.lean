/- Diagnostic shape from the historical completion report. -/

-- With `debug.skipKernelTC`, add:
-- noncomputable def DCC (K : DerivedCategory (Sheaf J (ModuleCat R))) :
--   Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := sorry
-- Then replay:
--   Kernel.check env default declaredType
--   Kernel.check env default value
--   Kernel.isDefEq env default inferredType declaredType
-- The recorded result is 3 ms, 3 ms, and >600 s respectively.

-- The proof-free control is:
-- axiom E21ax (K : ...) : Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K)
-- noncomputable def E21 (K : ...) : Cone (...) := E21ax J I K
-- It completes in 5.2 s and leaves no abstracted nested proofs.
