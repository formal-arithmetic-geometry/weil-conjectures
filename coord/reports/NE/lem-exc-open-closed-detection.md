## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection` states
`AlgebraicGeometry.Scheme.proEtaleRingModule_isZero_of_open_closed`, with `sorry`
as its whole proof. It detects zero module sheaves over arbitrary commutative
ring-sheaf coefficients, using the actual identified-coefficient operations.
No node correction, new definition, or dependency repair is needed.

Hypotheses and conclusion, clause by clause:

- Schemes and immersions: `{X Z U : Scheme.{u}}`, `i : Z ⟶ X`, `j : U ⟶ X`,
  `[IsClosedImmersion i]`, `[IsOpenImmersion j]`.
- The open immersion is quasi-compact as a morphism: `[QuasiCompact j]`.
  Neither quasi-compactness nor quasi-separatedness of X is assumed.
- Complementarity: `hU : Set.range j = (Set.range i)ᶜ` says precisely that the
  underlying images are complementary, allowing any presentation of the open subscheme.
- Arbitrary coefficient sheaf: `R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}`.
  No constant, finite, constructible, torsion, or nonzero-coefficient restriction occurs.
- The identified inverse-image coefficients of the node's operations are explicit:
  `Ri`, `Rj` are coefficient sheaves on Z and U, and `ci`, `cj` identify them with
  `(proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R` and the analogous j term.
  They are the given coefficient identifications, not extra conditions on R.
  Identity identifications and arbitrary isomorphic presentations are included.
- `F : proEtaleRingModules X R` is a sheaf of R-modules.
- `hj : IsZero ((proEtaleRingModulePullback j R Rj cj).obj F)` is `j^*F=0`.
- `hi : IsZero ((proEtaleRingModulePullback i R Ri ci).obj F)` is `i^*F=0`.
- `IsZero F` is the categorical assertion `F=0` (independent of a chosen zero object).

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleOperations`: `Scheme.proEtaleRingModules`,
  `Scheme.proEtaleRingModulePullback`, and its object construction
  `proEtaleRingModulePullbackObj`, which applies the recorded inverse image and
  `SheafOfModules.changeOfRings` along the specified coefficient isomorphism.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent Mathlib `SheafOfModules` specialization used by `proEtaleRingModules`.
- `def-weil-pbc-scheme-conventions` is a convention record, with no module or
  declaration. Its named Mathlib notions are used, notably `Scheme`,
  `IsClosedImmersion`, `IsOpenImmersion`, and `QuasiCompact`.
- Proof-only imports: `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`,
  `Scheme.proEtale_ringed_open_closed`; and `Mathlib.Algebra.Homology.ExactSequence`,
  `CategoryTheory.ComposableArrows.Exact`. The docstring gives the three proof
  steps in the DAG, including coefficient transport, localization, and exactness
  with zero end terms. The localization theorem's extra qcqs filtered-colimit clause
  is explicitly unused.

Source checked: the node's master-blueprint markdown and Stacks `proetale.tex`,
`lemma-ses-associated-to-open` (Tag 09AH), lines 5134 onward. Stacks assumes just
quasi-compactness of j for this sequence; linearity supplies the module version.

Edge cases checked mathematically before writing: U empty (closed part is all X),
Z empty (open part is all X), X empty, F zero, the zero coefficient sheaf, and
nonconstant coefficients. All are included and give the asserted conclusion.
Schemes live in universe u, the small pro-etale site's objects in u+1 and morphisms
in u, and coefficients/modules in u+1, exactly as the dependency definitions.
No equality of site object and morphism universes is imposed. The hypotheses
`hi` and `hj` are substantive vanishing assumptions, not automatic properties.

Searches for an existing statement:

- `msearch.py leanfinder`: “a module sheaf on the pro etale site is zero if inverse
  images to a closed immersion and its quasi compact open complement are zero”.
  Eight hits, including `Scheme.zero_of_zero_cover`, `exists_app_map_eq_zero_of_isLimit`,
  and etale-locus/support lemmas; no arbitrary ring-sheaf detection statement.
- `msearch.py loogle`: `SheafOfModules.pullback`. Twelve pullback construction,
  adjunction, identity and composition hits; no detection theorem.
- `msearch.py grep`: `isZero_of.*(upperStar|pullback|inverseImage)|open.*closed`,
  Mathlib `AlgebraicGeometry/Sites`: zero hits.
- `msearch.py leansearch`: “pro etale module sheaf open closed restrictions detect
  zero”: service unavailable (Internal Server Error).
- `rg` on upstream `WeilConjectures` and side `lean/WeilConjectures` found
  `ProEtale.isZero_of_isZero_upperStar_of_isCompl` in
  `SixFunctors/ProEtale/UpperLowerStar/ClosedImmersion.lean`. Its full signature
  uses `Sheaf (ProEt.topology X) (ModuleCat R)` for one fixed ring R. It does not
  give the node's arbitrary sheaf-of-rings version and cannot be attached as exact.
- `rg` for the node id confirms that same fixed-ring upstream attachment.
  `rg` in `lean/Sheaf` for ring-module zero/detection names finds no matching theorem.
  The existing general localization sequence was read and imported for the proof.

Validation: the delivered module is compiled using the prescribed `scompile.py`
wrapper, followed by `deliver2.py --no-push`. The second reader supplies the
independent reading and performs delivery; no second-reading claim is made here.


## Second reading by NE

I read the node statement, its Stacks source (Tag 09AH, `lemma-ses-associated-to-open`), the dependency signatures, and the delivered module item by item.

- Objects: the Lean binders `{X Z U : Scheme.{u}}`, `i : Z ⟶ X`, and `j : U ⟶ X` are exactly the closed and open immersions of the node. The typeclass binders `[IsClosedImmersion i]`, `[IsOpenImmersion j]`, and `[QuasiCompact j]` state precisely the source hypotheses; no quasi-compactness or quasi-separatedness of `X` is added.
- Complement: `hU : Set.range j = (Set.range i)ᶜ` expresses that the open is the complement of the closed subscheme, with no stronger equality of chosen subschemes.
- Coefficients: `R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}` is an arbitrary commutative ring sheaf, and `Ri`, `Rj` together with `ci` and `cj` are exactly the identified inverse-image coefficient sheaves and isomorphisms required by `def-weil-pbc-proetale-operations`. The universe choices match the pro-etale site convention.
- Module and hypotheses: `F : proEtaleRingModules X R` is the node's module sheaf; `hj` and `hi` state `IsZero` of the specified pullbacks along `j` and `i`, in the same order and with the same operations as the node.
- Conclusion: `: IsZero F` is exactly the categorical zero conclusion. There are no omitted clauses, extra assumptions, or strengthened quantifiers.

Edge cases checked are empty `U`, empty `Z`, empty `X`, zero `F`, zero or nonconstant coefficient sheaves, and identity or arbitrary isomorphic coefficient presentations. Each is admitted by the binders and has the stated zero conclusion when the two hypotheses hold. The index has no independent universe, so no case is excluded.

I repeated the existing-notion searches with `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`, plus LeanFinder/Loogle searches for pro-etale open/closed detection and `SheafOfModules` pullbacks. The only upstream hit, `ProEtale.isZero_of_isZero_upperStar_of_isCompl`, is for a fixed coefficient ring and does not state this arbitrary ring-sheaf theorem; no exact existing declaration was found. The dependency declarations `proEtaleRingModules` and `proEtaleRingModulePullback` were opened and match their use here.

No mismatch was found, so no statement, dependency, or module repair was required. The module compiled cleanly with `scompile.py`; the only postponed proof is the named theorem's `sorry`, with its source and step-by-step proof documented above. No new definition nodes or dependency modules were needed.
