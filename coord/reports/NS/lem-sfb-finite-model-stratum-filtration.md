## Worker report

The module `Sheaf.Paper.FiniteModelStratumFiltration` states
`AlgebraicGeometry.ProEtale.CondensedRing.exists_finiteModelStratumFiltration`.
Its only postponed proof is that theorem. Three auxiliary definitions have actual
construction data: `openFiltrationPiece` is the composite of the recorded module
pullback and extension by zero; `openFiltrationCounit` is the counit of their
canonical upstream adjunction; `openFiltrationStratum` is the composite
`v^* ⋙ t^* ⋙ t_* ⋙ v_!`. These are names for expressions in this theorem, not
replacement notions or independent DAG nodes. No target, dependency node or
natural-language statement is changed.

Source reading: Stacks `topology.tex`, Tag 09Y5,
`lemma-noetherian-partition-refined-by-stratification`, lines 5630--5664;
Tag 09Y0, `definition-good-stratification` and its following closure formula,
lines 5524--5547. Also `proetale.tex`, Tag 09AH,
`lemma-ses-associated-to-open`, lines 5134--5155, including the quasi-compact-open
hypothesis. The scalar-model condition was read in the current blueprint
`main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-constructible/_section.md`,
clauses (1)--(2), and in its recorded Lean definition. The resolved stage-1 repair
note for this item only concerns the earlier proof split; it requires no stage-2
interface repair.

Hypothesis and clause correspondence:

- Schemes and the fixed site universe: `X : Scheme.{u}`, with all stratum schemes
  also in `Scheme.{u}`. The module category is exactly
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
  This retains the framework's small-site object/morphism universe difference.
- Arbitrary commutative condensed ring: the section binder is
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. It is not restricted to continuous functions on a
  particular topological ring. The dependency's continuous-function example is
  not a hypothesis of this node; the generic ring-object interface is the one
  already used by its coefficient and constructibility dependencies.
- Coefficients `B_T=p_T^*Λ`: `condensedRingObj Λ T`, directly from the recorded
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` declaration.
- Noetherian underlying topology, rather than a locally Noetherian scheme:
  `[TopologicalSpace.NoetherianSpace X]`. Mathlib's
  `TopologicalSpace.noetherianSpace_TFAE` equates this with the descending-chain
  condition and compactness of every subset.
- Constructible F with the stated finite scalar models: the binder `F` in that
  module category and `hF : IsConstantModelConstructible Λ X F`. This is the
  recorded, stronger scalar-model notion, not upstream's general local finite
  presentation condition.
- A nonnegative integer and an increasing chain of opens:
  `∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), Monotone V`, with `V 0 = ⊥` and
  `V (Fin.last r) = ⊤`. Each `V k` is an actual open subscheme through
  `(V k).toScheme` and its canonical immersion `(V k).ι`.
- Reduced closed strata with exactly the differences as their underlying sets:
  `S : Fin r → Scheme.{u}`, `t : ∀ k, S k ⟶ (V k.succ).toScheme`, and
  `IsClosedImmersion (t k) ∧ IsReduced (S k) ∧ Set.range (t k) =
  {x | (V k.succ).ι x ∉ V k.castSucc}`. The difference is written in the
  ambient open, so the image comparison has the correct type.
- `L_k=t_k^*(F|V_k)` and its finite constant local model:
  `HasFiniteConstantLocalModel Λ (S k)
  ((upperStar Λ (t k)).obj ((upperStar Λ (V k.succ).ι).obj F))`.
- Quasi-compactness and quasi-separatedness of every open immersion to X:
  `∀ k, QuasiCompact (V k).ι ∧ QuasiSeparated (V k).ι`.
  For the complement of `t k`, the corresponding formula uses the canonical
  open immersion `((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι`. The stratum image equality
  makes this exactly the complementary open, not an unrelated choice.
- The objects `F_k=v_k!v_k^*F` and their maps to F are precisely
  `(openFiltrationPiece Λ (V k)).obj F` and
  `(openFiltrationCounit Λ (V k)).app F`. Their `Mono` clauses identify these
  objects with their counit images as subobjects of F.
- The zero and terminal pieces: `IsZero` of the piece at `V 0`, and `IsIso`
  of the counit at `V (Fin.last r)`. Thus the latter equality with F uses the
  specified embedding into F, rather than an unrelated object isomorphism.
- The nested subobjects are given by natural transformations `d k` between
  successive piece functors. Their components at F are monomorphisms, and
  `d k ≫ openFiltrationCounit Λ (V k.succ) =
  openFiltrationCounit Λ (V k.castSucc)` states compatibility with the
  actual embeddings into F. This is precisely the order relation of these
  subobjects, with a named representative arrow.
- The quotient formula and its naturality for fixed strata:
  `Nonempty (cokernel (d k) ≅ openFiltrationStratum Λ (V k.succ) (t k))`.
  This cokernel is taken in the abelian functor category of module-sheaf
  endofunctors. Cokernels are computed pointwise; its evaluation at F is
  `F_{k+1}/F_k`, and its isomorphism to the displayed composite is a natural
  isomorphism. Thus it includes the commutative square for every module-sheaf
  morphism with this filtration held fixed. It does not choose a stratification
  naturally in F, which the node does not request. The right-hand functor uses
  ordinary `lowerStar Λ (t k)`, not a derived functor.
- There is no local Noetherianity, finite-type-over-a-field, field coefficient,
  torsion-freeness or locally free hypothesis. The scalar-model predicate
  admits every finite presentation, including nonprojective torsion models.

Dependency declarations read and used:

- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and
  `HasFiniteConstantLocalModel`; their complete definitions use genuine covers
  and finite presentations on the point before pulling to the cover.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj` and
  `isCommMonObj_condensedRingObj` in namespace `AlgebraicGeometry.ProEtale`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar` and `lowerStar`.
  Their signatures and docstrings specify mapMod followed by extension along
  alpha or restriction along eta respectively.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek` and
  `openImmersionLowerShriekUpperStarAdjunction`; the former is precisely
  restriction along alpha followed by the linear extension by zero.
- Mathlib `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Scheme.ProEt` and its
  topology; `IsOpenImmersion` in `AlgebraicGeometry.OpenImmersion`;
  `IsClosedImmersion` in `AlgebraicGeometry.Morphisms.ClosedImmersion`;
  `QuasiCompact` in `AlgebraicGeometry.Morphisms.QuasiCompact`;
  `QuasiSeparated` in `AlgebraicGeometry.Morphisms.QuasiSeparated`;
  `IsReduced` in `AlgebraicGeometry.Properties`.
  The finite-type definition node supplies quasi-compactness only; no
  finite-type hypothesis is imported into the theorem.
- Mathlib `CategoryTheory.Abelian.FunctorCategory` supplies the abelian structure
  and pointwise cokernels on the endofunctor category.
- Every recorded proof dependency module available in the shared checkout is
  imported privately (or already included publicly through a statement import).
  This includes the topology refinement, reduced induced closed subscheme,
  reduced-source factorization, ringed open-closed sequence, internal/sectionwise
  equivalence, inverse-image functoriality, and adjoint composition isomorphism.
  The compactness lemma is a Mathlib leaf in `Mathlib.Topology.NoetherianSpace`.

Edge cases checked before writing: for the empty scheme take `r=0`; the two
endpoint indices then agree, all stratum and successive-arrow conditions are
vacuous, and its sheaf category has only zero objects up to isomorphism. A
one-stratum space permits `r=1`, with reduced stratum equal to the reduction of X;
no reducedness of X itself is required. Nonreduced X is allowed because only
S carries `IsReduced`. The zero module and the zero coefficient ring are
allowed. Torsion finitely presented scalar modules require no freeness or
flatness, since the local-model condition and the source proof use cokernel
presentations and exact inverse image. All endpoints use canonical morphisms.
There is no statement dispute or statement correction.

Searches run (not inferred from names):

- `msearch.py ... leanfinder "constructible sheaf finite open filtration reduced
  strata extension by zero subquotients"`: 8 hits, on constructible subset data
  and related topology; no matching module filtration statement.
- `msearch.py ... loogle "Subobject, cokernel"`: 0 hits; service reported unknown
  identifier `Subobject`. This search did not establish nonexistence.
- `msearch.py ... grep "stratum|stratification|[Ff]iltration" AlgebraicGeometry`:
  0 hits in the selected Mathlib directory.
- `msearch.py ... leansearch "constructible sheaf finite filtration extension by
  zero strata"`: 8 hits, on finite generation/presentation and sheaf colimits;
  no matching statement.
- `rg` over `WeilConjectures`, Mathlib and `lean/Sheaf` for the proposed four
  declaration names returned none. Broader finite-filtration/constructible
  searches returned spectral-sequence filtrations, coherent/integral
  filtrations, and the upstream general extension-closure predicate, not this
  scalar-coefficient open-closed filtration. Searching the item id in
  `WeilConjectures` and `dag/lean_names_upstream.json` returned no binding.

## Second reading by NS

NS reread the node and module for this packet; the maintainer supplies independent review. The declaration and statement are unchanged from the already published Q50 interface, so this packet only re-records the item for NS.
Reopened the node and the completed module. The topology hypothesis is only
NoetherianSpace, not scheme Noetherianity. The coefficients and both pullback
operations are the recorded internal module-object functors. In particular,
finite scalar models use the corrected constructibility dependency, not the
upstream arbitrary-coefficient finite presentations. Checked the Fin indexing:
`castSucc` is the earlier open and `succ` is the later open, so the difference,
restriction and quotient all have the intended direction. Checked the image
set lives in the later open. Checked that reducedness is on the stratum and
that all opens and complementary opens have both qcqs properties. Checked
that both zero and whole pieces use the very counit defining the subobject.
Checked the equation for d is equality of natural transformations into the
identity functor; it therefore identifies the actual nested subobjects.
Finally read the quotient as a cokernel in an abelian functor category, which
retains naturality for all morphisms with opens fixed and uses the ordinary
closed direct image. No mismatch requiring a node correction was found.

Validation: `scompile.py NS lem-sfb-finite-model-stratum-filtration` compiled
this module cleanly, including its private proof imports. The wrapper's separate
library-file check completed in 17.2 seconds. All source lines are at most 100
characters; `autoImplicit` is disabled and universe u is explicitly declared.
