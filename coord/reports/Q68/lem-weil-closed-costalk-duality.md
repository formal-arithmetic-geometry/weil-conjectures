## Worker report

The module `lean/Sheaf/SixFunctors/ClosedCostalkDuality.lean` states the two
alternatives of `lem-weil-closed-costalk-duality`:
`AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality_etale` and
`AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality` (pro-etale).
Both theorem proofs are `sorry`. Definitions have actual data. The node is
copied from the current shared repository with only its `lean` field changed.

The earlier attempt was not usable: arbitrary category types and arbitrary
functors called `iStar`, `dualT` and `dualZ` did not identify them with the
source's categories or operations. Even for the identity immersion, choosing
different constant dual functors on a discrete category contradicts that
signature. The purported statement correction merely removed information;
it did not repair that defect. This delivery discards that correction and
restores the reviewed coefficient/site expansion of the source. The current
blueprint's concise ambient assertion is read together with its defined
operations, not as a theorem about unrelated functors.

Clause-by-clause rendering:

* Schemes and closed immersion: `{T Z U : Scheme.{u}}`, `(i : Z ⟶ T)` and
  `[IsClosedImmersion i]` in both declarations.
* Complementary open: `(j : U ⟶ T) [IsOpenImmersion j]` and
  `_hij : Set.range j.base = (Set.range i.base)ᶜ`. In the pro-etale
  declaration `[QuasiCompact j]` is included, exactly as in the reviewed node.
  It is needed by the recollement argument, even though it does not occur
  in the final comparison's type.
* Choice of site: the two declarations give the etale and pro-etale cases,
  using `smallEtaleTopology` and `ProEt.topology`, respectively. Their module
  categories are `closedCostalkEtaleModules` and `proEtaleRingModules`, both
  transparent specializations of the recorded `ringedSiteModules`.
* Arbitrary commutative coefficient sheaf: the binder `R` is a sheaf valued
  in `CommRingCat.{u + 1}` on the chosen site. No finiteness or constant-ring
  hypothesis is imposed. The ring on Z is the actual ring inverse image:
  `closedCostalkEtaleRingPullback i` or `proEtaleSheafInverseImage i` applied
  to R. The auxiliary open ring in the node is similarly j inverse image;
  it is used only in the proof, so no unrelated open coefficient is a binder.
* Ordinary unbounded derived categories: `DerivedCategory` of these actual
  module categories, with the standard localization instances. No category
  of bounded, constructible, complete, or finite-Tor objects is substituted.
* Exact inverse image and termwise closed direct image: on the pro-etale
  side the existing `proEtaleRingDerivedPullback` and
  `proEtaleRingDerivedDirectImage` are used, with identity identification of
  the actual inverse-image coefficient ring. Direct image agrees with
  termwise descent because closed pushforward is exact, by the node's proof.
  On the etale side `closedCostalkEtaleModulePush` is the explicit Mathlib
  module pushforward with coefficient unit from the ring inverse-image
  adjunction. `_ai : iStar ⊣ closedCostalkEtaleModulePush i R` specifies the
  actual inverse image up to the unique isomorphism of left adjoints. The
  natural isomorphisms `_pullFactors` and `_pushFactors` identify iPull and
  iPush with their termwise complex functors after Q. Thus the derived
  functors are determined up to unique factorization isomorphism. These
  binders express the termwise descent specified in the node; they do not
  add a projection-formula or duality assumption. iStar additivity is part
  of this presentation of the exact inverse image and follows from its
  adjunction to additive pushforward.
* Ambient exceptional adjoint: `riExcl` has source and target these exact
  derived categories, and `_adj` is the adjunction with their actual closed
  direct image. It is assumed, as in the source; it is not inferred from
  constructible six-functor adjunctions.
* Any omegaT: `ωT` ranges over the whole ambient derived category. The
  equality omegaZ = Ri!omegaT is implemented by directly using
  `riExcl.obj ωT`, avoiding another unconstrained object.
* D_T and D_Z: `(𝟭 _).prod' ((Functor.const _).obj omega)` followed by
  `derivedInternalHomOfUniverses` is precisely the functor
  K ↦ RHom(K,omega), with its contravariant maps. Both internal Homs use
  the recorded K-injective construction, never arbitrary dual functors.
* Conclusion: `Nonempty (D_T ⋙ riExcl ≅ iPull.op ⋙ D_Z)` is a natural
  isomorphism on the opposite ambient category, hence all alpha_K and
  their naturality. The pro-etale version substitutes actual derived
  pullback for iPull. There are no biduality, boundedness, constructibility
  or finite-Tor assumptions on K or omegaT.

The six-step proof docstring retains the reviewed node's proof: closed
support, exact descent and pullback-tensor compatibility, the projection
map and open/closed cone detection, tensor-Hom via currying and global Hom,
the exceptional-adjunction Hom chain, and Yoneda with explicit inverse maps.
The pro-etale docstring explains the ringed recollement replacement for
etale geometric stalks. These are plans for stage 3, not additional theorems
assumed in the statements.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, closed embedding with surjective
  stalk maps (lines 43-46).
* `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `Scheme.smallEtaleTopology` (lines 50-53), with `Scheme.Etale` and the
  jointly-surjective covering characterization (lines 61 onward).
* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `Scheme.proEtaleDerivedCategory`, the standard module localization with
  canonical ULift constant coefficients; its site and size convention are
  retained while the present arbitrary coefficient sheaf uses ringed modules.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `HasDerivedCategory.standard`,
  and `DerivedCategory.Q` (lines 71-98).
* `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the exact Mathlib module-sheaf category.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, read with its full
  signature, K-injective localization construction, and comparison docstrings.
  Its site object universe is u+1, site morphism universe u, coefficient
  auxiliary universe 0 and localization morphism universe u+2. The max is
  u+1; no equality between site object and morphism universes is imposed.
* `Sheaf.AlgebraicGeometry.ProEtaleOperations`:
  `Scheme.proEtaleRingModules`, its standard localization instance,
  `proEtaleRingDerivedPullback`, and `proEtaleRingDerivedDirectImage`.
  Their full exact-descent and K-injective definitions were read. These
  specialize the ringed operations already used in the node's proof route.
* The remaining recorded proof-dependency modules are imported without
  `public`, including the current generalized global-Hom interface,
  ringed tensor-pullback module, termwise adjunction, closed essential image,
  ringed pro-etale recollement and geometric-stalk infrastructure. Mathlib
  cohomological detection and the distinguished-cone criterion are also
  imported. The specialized completed-pullback primary record is not
  misused as a general ringed adjunction; its published module retains the
  generic tools in its public import closure.

Edge cases checked: identity immersion gives RHom(K,omega) on both sides;
empty Z has the zero derived category and the unique isomorphism; empty U
and identity closed inclusion are allowed; zero omega and zero K are
allowed; arbitrary unbounded complexes are allowed. The comparison is
conditional on the ambient adjoint in every case. On the pro-etale side
an arbitrary non-quasi-compact open complement is deliberately not included,
exactly as in the reviewed node. The etale version does not impose that
restriction. No new notion or dependency repair is needed: the public helper
definitions specialize existing constructions in the owning node's module.

Searches performed for this repair:

* `msearch.py leanfinder`, query "natural isomorphism exceptional inverse
  image Verdier dual closed immersion": eight generic restriction and
  open-immersion hits, including restrictFunctorAdjCounitIso; no match.
* `msearch.py loogle`, query `CategoryTheory.Adjunction`: twelve generic
  adjunction hits, including Adjunction.id and mkOfHomEquiv; no comparison.
* `msearch.py grep`, query `Verdier|costalk|exceptionalRestriction`:
  25 capped hits on Verdier references and localization infrastructure,
  no internal-Hom exceptional comparison.
* `rg` over the upstream WeilConjectures tree and project lean/Sheaf for
  `lem-weil-closed-costalk-duality`, `exceptionalRestrictionVerdierDuality`,
  closedCostalk and costalkDual patterns: no matching declaration. Related
  operation modules were opened and reused, not copied.

The sandbox's earlier search log is retained. No unavailable service is
reported as a negative search. There is no STATEMENT-DISPUTED claim about the
reviewed node and no statement_change in this delivery.

Validation: the prescribed scompile.py compiles the module in both sandbox
and library module positions. The first dry run identified that the preflight signature reader excludes the trailing
`:=`; the record was adjusted accordingly. The second reading is left to the
independent reader, as required.

## Second reading by Q68

I read the node statement and the source place
`literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-weil-closed-costalk-duality.md`
(order 2125) before checking the Lean declarations. The source proof is the displayed
Hom chain followed by Yoneda; it assumes only the closed immersion, the complementary
open, the chosen etale or pro-etale ringed site (with quasi-compact complement in the
pro-etale case), the ordinary unbounded module-sheaf derived categories, exact
termwise inverse/direct images, and the ambient exceptional adjunction.

The node's objects and their Lean rendering are as follows.

* The schemes and maps are `{T Z U : Scheme.{u}}`, `(i : Z ⟶ T)`,
  `[IsClosedImmersion i]`, `(j : U ⟶ T)`, `[IsOpenImmersion j]`, and
  `_hij : Set.range j.base = (Set.range i.base)ᶜ` in both theorem declarations.
* The two site choices are rendered separately: `T.smallEtaleTopology` and
  `ProEt.topology T`, with the corresponding `closedCostalkEtaleModules` and
  `proEtaleRingModules`. The pro-etale declaration has `[QuasiCompact j]`, exactly
  the node's extra hypothesis; the etale declaration does not.
* The coefficient object is `R : Sheaf ... CommRingCat.{u + 1}`. Its closed-site
  coefficient is the actual inverse image
  `(closedCostalkEtaleRingPullback i).obj R` or
  `(proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R`. I added the definitional
  local `let ΛU := ...j...obj R` in each result type so the node's complementary
  coefficient sheaf `Λ_U = j⁻¹Λ_T` is present without adding an independent
  hypothesis or choice.
* `DerivedCategory` is used on those exact module categories, with the ordinary
  standard localization instances. The internal Hom is the recorded
  `derivedInternalHomOfUniverses` at the full site/coefficient universes, so the
  objects are the node's unbounded `R\mathcal Hom(-,ω)` constructions.
* The etale declaration presents exact inverse image and direct image through
  `iStar`, `iPull`, and `iPush`: `_ai : iStar ⊣ closedCostalkEtaleModulePush i R`,
  `_pullFactors` and `_pushFactors` identify their termwise complex functors with
  `DerivedCategory.Q`, and `_adj : iPush ⊣ riExcl` is precisely the ambient
  exceptional adjunction. These are presentation witnesses for the canonical
  operations, not extra finiteness, boundedness, constructibility, or Tor
  assumptions. The required additive instance on `iStar` is the structural
  additivity needed by the termwise complex functor.
* The pro-etale declaration uses the recorded canonical
  `proEtaleRingDerivedPullback` and `proEtaleRingDerivedDirectImage`, with
  `(_adj : ... ⊣ riExcl)`, so its inverse image and direct image are fixed rather
  than arbitrary functors.
* The dualizing object is `(ωT : DerivedCategory ...)`; `riExcl.obj ωT` is the
  node's `ω_Z = Ri^!ω_T`. The conclusion is a `Nonempty` natural isomorphism of
  functors on the opposite derived category. Its left side is
  `K ↦ Ri^! R\mathcal Hom(K,ω_T)` and its right side is
  `K ↦ R\mathcal Hom(i^*K,Ri^!ω_T)`, hence it packages exactly the node's
  natural `α_K` and all its naturality equations.

I found one statement rendering omission: the worker signature used `j` only in the
complement hypothesis and omitted the node's named complementary coefficient object
`Λ_U`. I repaired both theorem result types with the definitional `let ΛU` above and
updated the node's `lean.statement` verbatim to the pro-etale declaration. I also
tried removing `[iStar.Additive]`; Lean then correctly required
`iStar.PreservesZeroMorphisms` for `mapHomologicalComplex`, so I restored the
structural additive instance rather than weakening the termwise construction.
No node hypothesis was added or dropped, and no target statement or dependency was
changed.

For edge cases, the identity immersion and empty complement reduce to the identity
restriction comparison; an empty closed scheme gives the zero derived category and
its unique natural isomorphism; zero `K` and zero `ωT` are allowed; arbitrary
unbounded complexes are the quantified derived-category objects; the characteristic
is unrestricted; and the explicit universes retain site objects in `u+1` and site
morphisms in `u` on the pro-etale side. The pro-etale quasi-compactness condition is
retained, while the etale alternative has no such restriction.

I repeated the existing-definition searches. `msearch.py ... leanfinder` for
“exceptional restriction Verdier dual closed immersion” returned only generic closed
immersion and open-restriction declarations; the corresponding grep search for
`exceptionalRestrictionVerdierDuality|closedCostalk|costalkDual|VerdierDual` in both
`WeilConjectures` and `lean/Sheaf` found no declaration. The Mathlib grep for internal
Hom/exceptional-duality terms likewise found no match. The operation modules and
`derivedInternalHomOfUniverses` were opened and their exact signatures reused; no
second definition or dependency repair is needed.

After the repair, `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q68
lem-weil-closed-costalk-duality lean/Sheaf/SixFunctors/ClosedCostalkDuality.lean`
compiled the sandbox and library positions cleanly, with only the permitted `sorry`
warning.
