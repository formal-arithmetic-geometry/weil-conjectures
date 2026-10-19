## Worker report

The module `Sheaf.Paper.FiniteWindowUnbounded` states the node in two declarations:
`AlgebraicGeometry.ProEtale.finiteWindow_unbounded` for Λ=E and
`AlgebraicGeometry.ProEtale.finiteWindow_unbounded_padicAlgCl` for Λ=Qlb.
Both proofs are `sorry`; no mathematical assertion is proved and no definition is added.
The natural-language statement is unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `ℓ : ℕ` and `[Fact ℓ.Prime]` specify the prime. In the finite-extension case,
  `E : PadicAlgCl.FiniteIntermediateField ℓ` specifies a finite intermediate extension
  of Q_ℓ in the fixed algebraic closure, with its restricted norm topology.
- The condensed coefficients are `Profinite.continuousMapRingObj E` and
  `Profinite.padicAlgClRingObj ℓ`. The latter is specifically the condensed ring whose
  sections take values in a finite subextension, rather than all continuous maps into
  the valuation-topological algebraic closure. The algebraic-closure case needs no unused
  E binder, since E does not occur in that specialization of the node.
- `X : Scheme.{u}` is arbitrary: no Noetherian, finite-type, separated, base-field or
  cohomological-dimension assumption is imposed.
- `pulledBackModuleObjects Λ X` is the dependency's abbreviation for `Mod` over
  `coefficientRing X (Mon.mk Λ)`. Its underlying ring is `condensedRingObj Λ X`,
  definitionally `upperStarFromPoint X |>.obj Λ`, with transported monoid structure.
  Thus C and N are actual module sheaves over Λ_X, not constant-ring sheaf modules.
- `hC : IsConstantModelConstructible Λ X C` is exactly finite constant-model
  constructibility. Its qcqs branch uses a finite constructible locally closed
  `Scheme.Stratification` and `HasFiniteConstantLocalModel` on every stratum;
  its general branch imposes this on affine opens. This is the existing declaration
  of `sk-def-sfb-constructible`; that landed node is added to `stmt_deps` to record use
  of its interface. The local-model dependency identifies this with scalar-extension
  models from finitely presented Λ(*)-modules, not arbitrary variable local matrices.
- `d_C : ℕ` is exactly an integer ≥0. The bound `hExt` quantifies over every module N,
  assumes `IsConstantModelConstructible Λ X N`, and requires vanishing in every natural
  degree r with `d_C < r`. `Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r)`
  is vanishing of the actual Mathlib Ext group. `HasExt.standard` merely chooses the
  standard ambient size; it is an explicit term, not an added hypothesis. The canonical
  additive equivalence `Abelian.Ext.homAddEquiv` identifies this Ext with the ambient
  derived morphisms C[0] → N[0][r] of def-pc-ext.
- `L : DerivedCategory (pulledBackModuleObjects Λ X)` is the ordinary unbounded
  derived category. No derived completion, bounded subcategory, or alternative heart
  replaces it.
- `hL` requires every cohomology sheaf to satisfy `ObjectProperty.ind.{u+1}` of exactly
  `IsConstantModelConstructible Λ X`. Mathlib's `ind` quantifies over a small filtered
  category and a `ColimitPresentation` in this actual ambient module category, including
  invariance under sheaf isomorphism. This renders both IndCons and the definition of Dic
  inline using existing definitions, without creating a duplicate predicate.
- `hvanish` requires `IsZero (H^q(L))` exactly for `-(d_C : ℤ)-1 < q`. The use of ℤ
  avoids natural-number truncated subtraction. There is no lower bound on q or on L.
- `Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L)` is precisely
  Hom_D(C[0],L)=0: the Hom type is an abelian group and already contains the zero morphism.
  No claim that L itself vanishes is made.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, `condensedRingObj`,
  `upperStarFromPoint` and its transported monoidal structure.
- `Sheaf.Paper.ModuleObjects`: `CategoryTheory.moduleObjects` and
  `AlgebraicGeometry.ProEtale.pulledBackModuleObjects` (the recorded module-object category).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `HomologySequence`: `DerivedCategory.homologyFunctor`;
  `Ext.Basic`: `CategoryTheory.Abelian.Ext`, `HasExt.standard`, `Abelian.Ext.homAddEquiv`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification` (publicly imports the
  exact recorded general stratification interface; the constructibility definition
  separately uses the existing version with constructible strata).
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `AlgebraicGeometry.ProEtale.finiteConstantLocalModel_iff_exists_cover`, identifying
  the existing `HasFiniteConstantLocalModel` with the scalar-extension cover formulation.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`, `IsFiniteConstantStratified`,
  `HasFiniteConstantLocalModel`. No definition is copied.
- `Mathlib.CategoryTheory.ObjectProperty.Ind`: `CategoryTheory.ObjectProperty.ind`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension` and
  `EllAdic`: finite intermediate fields, `Profinite.continuousMapRingObj`,
  `Profinite.padicAlgClRingObj`. The qlbar node has no lean record but its closed
  slopmaster2 audit records the exact EllAdic declarations, used as instructed.

Proof dependency imports are non-public: `Sheaf.AlgebraicGeometry.ProEtaleLeftComplete`
(`left_complete_quasiIso`), `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`
(`products_derived`), `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`,
`Mathlib.CategoryTheory.Triangulated.Pretriangulated` (representable Hom exactness),
and `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`
(`TStructure.triangleLEGE_distinguished`). `det-finite-window-bounded` has no Lean
record or mathlib match, so no proof-only module can yet be imported; its exact role is
included in both theorem docstrings, following all six steps of the node proof.
The theorem does not need an assumed bounded-vanishing principle as an extra hypothesis.

Edge cases checked before writing: d_C=0 gives the correct cutoff -1 and only positive
Ext degrees; q=-d_C-1 is retained, while q=-d_C is forced zero. Zero C, zero L, and the
empty scheme introduce no excluded case. Arbitrarily negative cohomology is allowed.
N ranges over all constructibles, including zero. The finite truncation interval in the
proof may be empty. The filtered index universe is u+1, the fixed coefficient-sheaf size
used by the existing neighboring ind-constructible statements, with no unrelated small
universe that could make the quantification vacuous. Every universe and variable is bound;
there are no local instances, private copies, local notation or let binders.

Searches (2026-10-18):

- msearch leanfinder: “Ext vanishing bound implies no morphisms from a constructible sheaf
  to an unbounded below complex”: eight hits, including
  `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`,
  `DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`, and dimension
  criteria. These require projectivity or concern a different direction of t-structure
  orthogonality, rather than this relative constructible Ext bound.
- msearch loogle: `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`:
  one exact-name hit, requiring projectivity, not a match for the node.
- msearch grep in Algebra/Homology/DerivedCategory:
  `from_singleFunctor_obj_eq_zero_of_projective|subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`:
  five hits in TStructure, Fractions, Ext/EnoughProjectives and Ext/Basic; no match.
- msearch leansearch: “vanishing Hom from a constructible sheaf to an unbounded below
  complex under a uniform Ext bound”: eight hits on injective/projective dimensions,
  boundedness and Hom sizes; none has these coefficients and relative Ext assumptions.
- rg in source WeilConjectures and project lean/Sheaf for
  `det-finite-window-unbounded|finite_window|finiteWindow`: no existing statement.
  grep for the exact node id in source WeilConjectures: no hit.
- rg for `IndConstructible|indConstructible|HasFiniteConstantLocalModel|IsConstructible`
  located the existing constructibility and ind-closure interfaces used here; neighboring
  bounded compactness and filtered-colimit theorems are distinct statements.

No statement dispute or correction. No new nodes or dependency repairs are needed.

Validation: `scompile.py NV det-finite-window-unbounded` compiled the delivered file
cleanly (21.0 seconds for the library-file check, plus its wrapper sandbox check).
No errors or warnings were emitted. The prescribed `deliver2.py NV det-finite-window-unbounded --no-push` dry run
reported OK: the commit passes preflight and compiles.
The maintainer supplies the independent second reading.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
