## Worker report

The module `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel` states
`AlgebraicGeometry.derivedInternalHom_of_boundedAbove_finiteFree`, with its sole proof
`sorry`. No notion is defined again and no mathematical statement is changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The ringed space `(U,O_U)` is `U : AlgebraicGeometry.RingedSpace.{u}`. This is
  Mathlib's abbreviation for `SheafedSpace CommRingCat`, with no local-ring condition.
- Its module category is `SheafOfModules.{u} (moduleRings U)`. The shared abbreviation
  `AlgebraicGeometry.moduleRings` from `Sheaf.Paper.DerivedHomMayerVietoris` is exactly
  `(sheafCompose (Opens.grothendieckTopology U) (forget₂ CommRingCat RingCat)).obj U.sheaf`.
  This import is used only for that existing structure-sheaf abbreviation; the
  Mayer–Vietoris theorem supplies no hypothesis or conclusion here.
- `E G K : CochainComplex ... ℤ` are the given cochain complexes of module sheaves.
  `K` has no additional boundedness hypothesis.
- Bounded above for `E` is `hEbounded : ∃ N, ∀ p, N < p → IsZero (E.X p)`.
- Finite-rank free terms are `hEfree : ∀ p, ∃ r : ℕ, Nonempty
  (E.X p ≅ SheafOfModules.free (R := moduleRings U) (ULift.{u} (Fin r)))`.
  Thus the rank can vary with degree, and freeness is freeness of the sheaf, not merely
  of its global sections or stalks. Mathlib's `free` is a coproduct of copies of the
  unit structure module; the unit is `O_U`. `ULift` changes only its index universe.
- Bounded below for `G` is `hGbounded : ∃ M, ∀ q, q < M → IsZero (G.X q)`.
- The given quasi-isomorphism `E → K` is `(f : E ⟶ K) [QuasiIso f]`.
- The total sheaf Hom complex is the existing `CategoryTheory.homComplex
  (R := U.sheaf) E G`, localized by `DerivedCategory.Q.obj`.
- The derived internal Hom is the existing `CategoryTheory.derivedInternalHom
  (Opens.grothendieckTopology U) U.sheaf`, evaluated at `(op (Q.obj K), Q.obj G)`.
  `Nonempty (... ≅ ...)` says precisely that the former complex represents the latter
  derived object. The node does not require a specified comparison morphism or naturality.
- `HasDerivedCategory.{w}` chooses the localization universe required by the recorded
  dependency. It imposes no additional geometric property. The opens site is small
  and both the ring sheaf and module sheaves have universe `u`, so the Hom-complex
  output universe `max u u u` is again `u`. Every variable and universe is explicit.

Dependency declarations read and used:

- `def-weil-locally-ringed-space-morphism`: Mathlib's
  `AlgebraicGeometry.LocallyRingedSpace.Hom` in
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace` extends the underlying ringed-space
  morphism with local stalk maps; here only its node's ringed-space notion is needed,
  supplied by `AlgebraicGeometry.RingedSpace` in `Mathlib.Geometry.RingedSpace.Basic`.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, with `val` a presheaf of modules and
  `isSheaf` its sheaf condition; its morphisms are maps of presheaves of modules.
- `def-pur-derived-internal-hom`: `CategoryTheory.derivedInternalHom` in
  `Sheaf.Algebra.Homology.DerivedInternalHom`, defined by localization of the fixed
  K-injective-replacement Hom bifunctor. Its `derivedInternalHom_obj_iso` signature
  and docstring were also read. The imported `CategoryTheory.homComplex` and
  `homComplexFunctor` in `Sheaf.Algebra.Homology.HomComplex` supply the specified
  product totalization and signed differential, with no replacement definition.

Edge cases: `r = 0` is included (the zero free module); zero complexes and an empty
space are included; all bounds are arbitrary integers, including negative integers.
Neither complex is required to be bounded on both sides. In each total degree only
finitely many factors can be nonzero because `E` is bounded above and `G` bounded below.
There is no field, characteristic, affineness, Noetherian or stalk-locality hypothesis.

Searches (real results retained in `searches.jsonl`):

- `msearch.py leansearch`, query `bounded above finite free sheaf Hom complex computes
  derived internal Hom`: unavailable, Internal Server Error.
- `msearch.py leanfinder`, same query: eight hits, principally
  `SheafOfModules.freeHomEquiv` and `CategoryTheory.Sheaf.H`; none states this result.
- `msearch.py loogle`, query `CochainComplex, QuasiIso`: shift/truncation
  quasi-isomorphisms and `DerivedCategory.isIso_Q_map_iff_quasiIso`; no match.
- `msearch.py grep`, query `internalHom|homComplex`, subtree `Algebra/Homology`:
  external Hom cochains and K-injectivity, not this sheaf-valued statement.
- `rg` on `WeilConjectures` and `lean/Sheaf`, query
  `lem-sc-derived-hom-finite-free-model|finite.*free.*[Hh]om|homComplexFunctor`:
  no existing declaration of this theorem; found the shared Hom-complex modules and
  sibling `BoundedAboveFiniteFreeHomAcyclic` and `FiniteFreeInternalHomExact`.
- `rg` for the proposed declaration name in `dag/lean_names_upstream.json`, upstream
  `WeilConjectures`, and `lean/Sheaf`: no collision.

Source check: local `literature/stacks-project/` is absent on this machine. Read the
source directly at https://stacks.math.columbia.edu/tag/0GM8 (case (2)), its proof's
reference https://stacks.math.columbia.edu/tag/0GM7, and the construction at
https://stacks.math.columbia.edu/tag/08J7. The bounded-below cone calculation is also
spelled out in the already-landed sibling `BoundedAboveFiniteFreeHomAcyclic`.
The module docstring reproduces all three proof steps and their node references.
No statement fault or dispute was found.

Validation: the server single-file compiler passed in 2.7 seconds with no errors or
warnings. The independent second reading remains for the second worker.

## Second reading by M1

I independently read the delivered node and Lean module, all three statement
 dependency nodes and their recorded declarations, the shared Hom-complex and
 derived-internal-Hom modules, and the Mathlib ringed-space, module-sheaf and free
 sheaf definitions. There are no new nodes, dependency modules, or statement
 corrections in this delivery.

The node's object/hypothesis/conclusion list and its Lean rendering:

1. A ringed space `(U,O_U)`: `(U : RingedSpace.{u})`. PASS.
   `Mathlib.Geometry.RingedSpace.Basic` defines it as a sheafed space of
   commutative rings. The cited dependency includes this ringed-space notion;
   its recorded `LocallyRingedSpace.Hom` adds stalk locality for morphisms, which
   the present node does not request. No locality condition is imported into
   the theorem's hypotheses.
2. Three cochain complexes of `O_U`-modules, `E`, `G`, and the target `K` of the
   quasi-isomorphism: `E G K : CochainComplex (SheafOfModules.{u}
   (moduleRings U)) ℤ`. PASS. `SheafOfModules` has the presheaf of modules and
   sheaf-condition fields, with linear natural transformations as morphisms.
   The dependency's `lean.note` explicitly retains its general-site Mathlib
   match, rather than restricting use to its recorded scheme specialization.
   `moduleRings` is the shared abbreviation in DerivedHomMayerVietoris, obtained
   by forgetting commutativity from `U.sheaf`; it does not change the ring.
3. `E` bounded above: `hEbounded : ∃ N : ℤ, ∀ p : ℤ,
   N < p → IsZero (E.X p)`. PASS: vanishing of terms, not just cohomology;
   no lower bound imposed.
4. Every term of `E` finite-rank free: `hEfree : ∀ p : ℤ, ∃ r : ℕ,
   Nonempty (E.X p ≅ SheafOfModules.free (R := moduleRings U)
   (ULift.{u} (Fin r)))`. PASS. Mathlib Free.lean:39 defines `free` as the
   coproduct of copies of the structure module `unit R`. This expresses a
   globally free sheaf on U, exactly the node's free (not locally free) terms;
   ranks can depend on p. No chosen bases or constant rank across degrees.
5. `G` bounded below: `hGbounded : ∃ M : ℤ, ∀ q : ℤ,
   q < M → IsZero (G.X q)`. PASS: no upper bound, no injectivity assumption.
6. A quasi-isomorphism `E → K`: `(f : E ⟶ K) [QuasiIso f]`.
   PASS: the actual chain map has the specified direction. K has no termwise
   boundedness or freeness requirement.
7. The total sheaf Hom complex represents derived internal Hom of K and G:
   `Nonempty (DerivedCategory.Q.obj (CategoryTheory.homComplex
   (R := U.sheaf) E G) ≅ (CategoryTheory.derivedInternalHom
   (Opens.grothendieckTopology U) U.sheaf).obj
   (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj G))`. PASS.
   I read `homComplex_exists`, `homComplexFunctor`, and `homComplex`: their
   product terms are Hom(E^p,G^(p+n)), with differential d_G f - (-1)^n f d_E.
   `derivedInternalHom` localizes this same bifunctor after a functorial
   K-injective replacement in the second variable. Thus the two sides use
   the same structure sheaf and module category. The node asks for
   representation, not a specified canonical map or a natural isomorphism
   of bifunctors. Objectwise `Nonempty` of an isomorphism is exactly that clause.
8. Localization infrastructure: `[HasDerivedCategory.{w} ...]`. PASS.
   Mathlib Basic.lean:74 defines this as a chosen localization;
   `HasDerivedCategory.standard` supplies one in the standard universe.
   This is inherited from the recorded derived-Hom dependency and adds no
   finiteness or geometric condition. All u and w occurrences are bound.

Source reading: the local Stacks .tex checkout is absent, so I read the raw
`cohomology.tex` and `sites-cohomology.tex` from the Stacks project repository,
including `lemma-stalk-internal-hom` (0GM8),
`lemma-pullback-internal-hom` (0GM7), `lemma-Rhom-strictly-perfect`, and
`section-internal-hom` (08J7). Also read the displayed tag pages:
https://stacks.math.columbia.edu/tag/0GM8,
https://stacks.math.columbia.edu/tag/0GM7,
https://stacks.math.columbia.edu/tag/08J7.
0GM8 itself states a stalk comparison, not this extracted supporting lemma;
its case (2) reduces through 0GM7 to local finite free models and bounded-below
second objects. The present node states the supporting computation on an
already chosen U and model E, so no stalk point or flat map belongs here.
The strictly perfect calculation and the construction in 08J7 assume only a
ringed space/site; no Noetherian, field, characteristic, or affineness condition
is implicit. The node's three-step cone proof extends the bounded strictly
perfect calculation to bounded-above E and bounded-below G: finitely many
nonzero factors occur in each total degree. I also read the landed
`acyclic_homComplex_of_boundedAbove_finiteFree` signature and its finite-local-
refinement proof, which supplies precisely the required bounded-below cone
calculation. All three node proof steps and cited nodes appear in the theorem
 docstring.

Edge cases: rank zero uses `ULift (Fin 0)`, an empty coproduct. Zero complexes,
empty ringed spaces (hence empty schemes), and zero structure rings are not
excluded. Bounds N and M are arbitrary integers, including zero and negative
values. For degree n the possible nonzero factors satisfy M-n ≤ p ≤ N;
if that interval is empty, the Hom term is zero. No field or nonzero-ring
assumption restricts characteristic. `u` is arbitrary, so objects with
originally different size bounds can be placed in a common universe; the
opens site and rings fit that universe and the Hom output is max u u u = u.
The independent w controls localization morphism size, not test-object
quantification. There are no unbound variables or local notations/instances.

Independent searches (different wording from the worker; results recorded by
msearch.py in searches.jsonl):

- LeanFinder: `sheaf valued derived Hom computed by free complex bounded above
  bounded below target`: eight hits, including Sheaf.H, Ext and object-level
  ProjectiveResolution.extMk_hom; none states this sheaf-valued computation.
- Loogle: `SheafOfModules.free`: twelve hits giving free sheaves, their
  sections/universal properties, and free functors; no derived-Hom theorem.
- LeanSearch: `internal sheaf Hom total complex finite free resolution computes
  derived Hom`: unavailable (Internal Server Error); no no-match verdict
  inferred from the unavailable service.
- Direct rg in Mathlib Algebra/Homology, upstream WeilConjectures, and project
  lean/Sheaf for `finite.*[Ff]ree.*[Hh]om`, `[Hh]om.*finite.*[Ff]ree`,
  `boundedAbove.*[Hh]om`, and `derivedInternalHom_of`: found the shared
  HomComplex/DerivedInternalHom definitions and the acyclic-Hom and exactness
  siblings, not the present representation theorem. The upstream tensor
  regularity theorem is about modules, not derived sheaf Hom.
- Exact-name rg in dag/lean_names_upstream.json, upstream WeilConjectures and
  project lean/Sheaf found no collision for
  `AlgebraicGeometry.derivedInternalHom_of_boundedAbove_finiteFree`.

Mismatches and repairs: none in the node or Lean statement. Kept the correct
module and lean.statement unchanged; appended this independent review.
No data definition is introduced, and the sole theorem proof is `sorry`.
Imports each serve an identifier in the statement. Source/blueprint docstrings,
proof steps, and line-length conventions checked.
