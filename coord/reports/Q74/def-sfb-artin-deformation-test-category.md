## Worker report

The module Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory supplies every
notion in def-sfb-artin-deformation-test-category. It preserves the node statement
and all existing dependencies. No statement correction, dependency repair, or new
notion node is needed. Helpers are parts of the constructions explicitly defined
by this item, and all are listed in lean.declarations. No mathematical result is
proved; every construction proof obligation is a named theorem with sorry and a
source and full natural-language proof in its docstring, attached to this node.

Clause-by-clause reading (namespace AlgebraicGeometry.ArtinDeformation):

- The base is `R k : Type u`, `[CommRing R]`, `[IsNoetherianRing R]`, `[Field k]`,
  `[Algebra R k]`, `[Algebra.FiniteType R k]`. The constructions whose data do not
  depend on Noetherianity or finite generation are usable more generally, with the
  identical definition; Lean omits unused section instances from their signatures.
  No finite-module hypothesis on k/R is introduced. This matters, for instance,
  for R = Z_(p), k = Q. Algebra maps are Mathlib unit-preserving `AlgHom`.
- `IsTestAlgebra` requires `IsLocalRing`, `IsArtinianRing`, and an augmentation
  `p : A →ₐ[R] k` that is surjective and has maximal-ideal kernel. First isomorphism
  gives exactly the specified R-algebra isomorphism A/m_A ≃ₐ[R] k, and conversely
  such an isomorphism gives exactly this p. No choice of a coefficient-field
  embedding k → A is assumed. Mathlib's local ring predicate is equivalent to a
  unique maximal ideal; Artinian is DCC on submodules/ideals of A.
- `TestCategory` is the full subcategory of `Over (CommAlgCat.of R k)` cut out by
  `IsTestAlgebra`. Its arrows commute with p. Thus they preserve the residue
  marking, and their inverse image of m_B is m_A: both are the kernel of the
  composite augmentation. Locality is automatic, not an extra assumption.
  `ring`, `residue`, and `map` expose these actual rings and algebra homomorphisms.
- `IsSmallExtension` is surjectivity, nonzero principal kernel, and annihilation
  of every kernel element by every element of m_B. This is Tag 06GD's precise
  definition and equivalent to the node's one-dimensional k-vector kernel:
  annihilation makes the B-action descend through B/m_B ≃ k; a nonzero principal
  generator is then a k-basis. The identity map is therefore not small.
- A groupoid is Mathlib's existing `IsGroupoid`, asserting every arrow in the
  existing category is invertible. `CofibredGroupoids` consists of a covariant
  `Pseudofunctor (LocallyDiscrete (TestCategory R k)) Cat.{v,w}` and groupoid
  predicates on its existing fibre categories. This does not replace their Hom
  types by some unrelated groupoid structure. `push` is transport. `unitIso`
  is (id)_* ≅ Id, and `compIso` is the inverse of Mathlib's oplax-oriented
  mapComp, hence f_* ⋙ g_* ≅ (f ≫ g)_*. Mathlib's unitor and associator axioms
  are exactly both unit equations and the associativity equation in the node.
- `residueTest` is the actual field with identity augmentation.
  `IsPredeformation` says the groupoid there is nonempty and every Hom has a
  unique element, exactly equivalence to the one-object one-arrow groupoid.
- `fibreProductAlgebra f₁ f₂` is the equalizer subalgebra of the two composites
  from ring A₁ × ring A₂: its elements are precisely the pairs f₁(a₁)=f₂(a₂),
  and its operations are the componentwise ones. `fibreProductResidue`,
  `fibreProductTest`, `fibreProductFst`, and `fibreProductSnd` give its actual
  marking and projections when f₂ is onto. `comparison` uses these projections,
  the commuting-square equality and only the transport composition constraints.
  Its codomain is Mathlib `CategoricalPullback`, whose objects are the node's
  triples (u₁,u₂,α) and arrows its compatible pairs. `IsRimSchlessinger` says
  this exact comparison is `Functor.IsEquivalence`, i.e. fully faithful and
  essentially surjective. No arbitrary equivalence functor or unconstructed
  fibre-product presentation is substituted.
- `isoClasses` is Mathlib's quotient by `isIsomorphicSetoid`.
  `squareZeroAlgebra` is literally `TrivSqZeroExt k V`, equipped with the
  canonical right k-action and the R-structure restricted through k.
  `squareZeroResidue` is its first projection. `squareZeroTest` assumes
  `FiniteDimensional k V` and packages precisely k[V], with Mathlib's
  multiplication (a,v)(b,w)=(ab,aw+bv). `tangentSet` is isoClasses at
  `squareZeroTest k`, namely F̄(k[ε]); it can in particular be used whenever
  `IsPredeformation F` holds.
- Complete marked local algebras reuse the already published
  `CategoryTheory.StackVersal.CompleteLocalAlgebra` from
  `Sheaf.AlgebraicGeometry.StackVersalFiniteResidueExtension`, with fields
  ring, localRing, noetherian, complete, residueEquiv. Its `complete` is
  `IsAdicComplete (maximalIdeal ring) ring`, equivalent to bijectivity of the
  canonical map to `AdicCompletion`; no arbitrary completion map is used.
  The same published module's `Level`, `levelResidue`, `reduction`,
  `KillsLevel`, and `evaluationMap` are used directly. These are existing
  auxiliaries of another item, not additional hypotheses or theorem inputs.
  That item's theorem is not added as a dependency: it depends transitively
  on this item, whereas its existing construction auxiliaries need none of
  this item's statements. A later library refactoring can extract those
  auxiliaries without redefining their mathematical notion.
- `levelTest C n` uses exactly C/m_C^(n+1). Its marking is the specified residue
  map composed with the quotient factor. `levelMap C h` is the quotient factor
  from a higher positive level to a lower one.
- `FormalObject F C` has objects at every positive level (n encoded by n+1) and
  transition isomorphisms for all m≥n. `transition_id` and `transition_comp`
  say they are obtained by the prescribed composition constraints. Storing
  all transitions with these equations is equivalent to storing successive
  transitions and defining their composites. `FormalHom` is a family of
  arrows satisfying precisely the transition commutation equation.
- `LocalMap C A` has an actual R-algebra map, locality, and preservation of
  the specified residue marking. `nilpotenceIndex A := Nat.find ...` is the
  predecessor of the least positive N with m_A^N=0. `evaluationAlgebraMap`
  is the actual quotient lift at that N; `evaluationMap` is its marked-test
  arrow. `evaluate ξ a` is its pushforward of ξ_N, exactly the fixed-level
  evaluation required in the node.
- `evaluationAtMap` composes reduction with that same quotient lift;
  `evaluationFromHigher` is the inverse composition constraint followed by
  transport of the formal transition. `evaluationRestriction` uses the
  common higher index max(N_A-1,N_B-1), these same comparisons, and equality
  of the induced quotient maps. This fixes the restriction isomorphism.
- `IsVersal ξ` quantifies over all surjections B→A, all local marked a:C→A,
  all y∈F(B), and each specified α:f_*y≅ξ_A. It requires a local marked
  lift b, the equality f∘b=a, and β:y≅ξ_B with
  f_*(β.hom) ≫ evaluationRestriction.hom = α.hom. This retains the specified
  α; it is stronger than merely finding an unrelated isomorphism downstairs
  and is exactly the required lifting property.

Dependencies inspected and used:

- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`, ideals finitely generated.
- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  `LocallyOfFiniteType`, `QuasiCompact`. For affine spectra the ring-side
  form is `Algebra.FiniteType R k`; it does not mean a finite field extension.
- def-weil-size-convention is metatheoretic. Explicit universes u,v,w give
  rings in Type u, test objects in Type (u+1), and fibre objects/Homs in w/v.
  There is no independent smaller test-ring universe that makes tests vacuous.
- Mathlib.RingTheory.AdicCompletion.Basic: `AdicCompletion`, `IsAdicComplete`.
- Mathlib.LinearAlgebra.FiniteDimensional.Defs: `FiniteDimensional`.
- Mathlib.Algebra.TrivSqZeroExt.Basic: `TrivSqZeroExt`, `fstHom`.
- Mathlib.RingTheory.HopkinsLevitzki: the recorded Artinian-to-Noetherian instance
  and `isArtinianRing_iff_isNilpotent_maximalIdeal`. They give the construction
  obligation `nilpotence_exists`, whose proof is postponed, not its data.

Edge cases checked against the definitions: zero rings cannot be test objects
(the marking is onto a field and local rings are nontrivial); the residue test
is present; V=0 gives k[0]=k; V=k gives dual numbers; positive levels start at
C/m_C, never the zero quotient C/m_C^0. A=k has nilpotenceIndex=0, meaning N=1.
The identity is not a small extension; k[t]/t³→k[t]/t² is. An empty fibre away
from k is allowed by `CofibredGroupoids`; `IsPredeformation` imposes nonemptiness
only at k. Differing nilpotence exponents and identity maps are covered by the
common higher evaluation construction and identity coherence. No characteristic
or residue-field splitting assumption was introduced.

Searches actually run using the prescribed msearch.py wrapper:

- leanfinder: "Artinian local test algebras fixed residue field groupoid
  predeformation formal object versal" — 8 hits, residue-field unramifiedness,
  IsLocallyArtinian and formal smoothness; none defines this framework.
- loogle: "CategoryTheory.Pseudofunctor, IsLocalRing.ResidueField, TrivSqZeroExt"
  — 0 hits for this combined query; the primitive definitions were opened
  directly in Mathlib and reused.
- grep: "Predeformation|ArtinTest|FormalObject|[Vv]ersal|Schlessinger" — 25 hits,
  all spurious universal/transversal substring hits. A narrower rg for
  predeformation, Predeformation, ArtinTest, FormalObject, Schlessinger and
  the node id in both lean/WeilConjectures and lean/Sheaf found the existing
  stack-fibre FormalObject and IsVersal, inspected in full. Those use objects
  in a given scheme stack with a chosen special-fibre point, rather than a
  pseudofunctor over C_{R,k}; they do not define this node. Their complete
  local algebra and quotient-map constructions are exact matches and reused.
- leansearch: "A groupoid valued pseudofunctor on marked Artinian local
  algebras, formal objects and versality" — 8 hits, general pseudofunctors,
  descent and groupoids; no marked test category or versality definition.
- rg of dag/lean_names_upstream.json and the two project source directories
  for CofibredGroupoids, ArtinDeformation and IsTestAlgebra found no duplicate.
  Narrow searches also inspected the general Mathlib Pseudofunctor,
  LocallyDiscrete, Cat, CategoricalPullback and isIsomorphicSetoid interfaces.

All module declarations have source and blueprint docstrings. The named
postponed construction obligations are field_isTestAlgebra,
fibreProduct_isTestAlgebra, fibreProduct_projection_residue,
fibreProduct_condition, squareZero_isTestAlgebra, level_isTestAlgebra,
reduction_residue, levelMap_refl, levelMap_comp, nilpotence_exists,
evaluation_kills, evaluation_residue and evaluationAtMap_comp. Each expresses
only the proof required to package the fixed, explicitly constructed data.
There is no choice of undetermined data from a sorry-backed existence theorem.
No STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled both the sandbox and the named library module
cleanly under the default per-file limit. Every variable/universe is explicitly
bound, with autoImplicit disabled. The prescribed deliver2.py --no-push dry run passed on 2026-10-24:
commit 4b09b170877 passed the server preflight and compiled; nothing was pushed
by that dry run. The delivery wrapper rechecks the final report and module.

## Second reading by Q74

This is the dispatcher's single-worker delivery, as explicitly requested; no
second agent was started and no independent review is claimed here. I reread
the node and the complete module clause by clause as documented above. During
that rereading I replaced the initial presentation-based RS predicate by the
actual fibre-product algebra and projections, avoiding any possible vacuity.
I also replaced a potentially independent groupoid structure on each fibre by
IsGroupoid on its existing Cat category and retained the given isomorphism in
the versality equation. The maintainer's independent review remains the second
reader of the delivered statement.
