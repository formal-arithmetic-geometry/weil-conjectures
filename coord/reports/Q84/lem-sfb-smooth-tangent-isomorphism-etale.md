## Worker report

The module Sheaf.AlgebraicGeometry.SmoothTangentIsomorphismEtale states
AlgebraicGeometry.etale_of_bijective_rational_tangentMap. Its only proof is `sorry`.
No definitions, helper nodes, dependency repairs or statement corrections are needed.
The original node changes only in `lean`.

Hypothesis and clause correspondence:

- The algebraically closed field k is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The schemes are `(X Y : Scheme.{u})`; the k-scheme structures are the explicit
  maps `pX : X ⟶ Spec (.of k)` and `pY : Y ⟶ Spec (.of k)`.
- Smoothness is `[Smooth pX] [Smooth pY]`.
- Finite type is `[LocallyOfFiniteType pX] [QuasiCompact pX]` and the corresponding
  two instances for pY, exactly the conjunction prescribed by the finite-type node.
- The k-morphism is `(f : X ⟶ Y) (hf : f ≫ pY = pX)`.
- Every rational point is quantified by `∀ x : X,
  Function.Bijective (pX.residueFieldMap x).hom → ...`. The domain residue field
  of this structural map is that of Spec k at its unique point, canonically k.
  This condition therefore says exactly that the structural map k -> κ(x) is
  an isomorphism. Such points correspond bijectively to X(k), with no choices
  of an unrelated residue-field isomorphism. For a k-morphism the image of a
  rational point is rational, since its structural field map factors through
  κ(f(x)) -> κ(x), both field maps being injective, and the composite is onto.
- The differential is the recorded canonical `schemeTangentMap k X Y pX pY f hf x he`.
  Its `he` argument is the bijectivity of the canonical residue map of f.
  The existential `∃ he : Function.Bijective (f.residueFieldMap x).hom, ...`
  merely supplies this automatically available identification at a rational point.
  The map is linear over κ(x), with target scalars transported through that
  identification; restriction along k -> κ(x) makes it precisely k-linear.
  `Function.Bijective` on this linear map is equivalent to existence of its
  linear inverse, so it states exactly that df_x is a k-linear isomorphism.
- The conclusion is `Etale f`.
- There is no nonemptiness, connectedness, fixed relative dimension, separateness,
  or characteristic hypothesis.

Statement dependencies read and reused:

- Mathlib.Algebra.Field.Defs: Field (available through IsAlgClosed.Basic).
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed; the algebraic-closure node
  explicitly records this as its algebraically closed field notion. The construction
  AlgebraicClosure and IsAlgClosure were also inspected but are not needed here.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: AlgebraicGeometry.LocallyOfFiniteType.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: AlgebraicGeometry.QuasiCompact.
- WeilConjectures.AlgebraicGeometry.SchemeTangentSpace: schemeTangentSpace,
  schemeTangentSpaceAddCommGroup, schemeTangentSpaceModule, schemeTangentMap;
  the full definitions and docstrings were read. No private tangent-space copy is used.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: AlgebraicGeometry.Etale.

Proof imports preserve the recorded proof plan: Kaehler.Basic, Dual.Lemmas,
AlgClosed.Basic, Morphisms.Basic, WeilConjectures.AlgebraicGeometry.Modules.Differentials,
Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality and
Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials. In particular these give
KaehlerDifferential, Scheme.Hom.relativeDifferentials,
rational_tangent_cotangent_duality,
LinearMap.dualMap_injective_iff, Module.Projective.exists_dual_ne_zero,
Scheme.exists_etale_open_of_coordinate_differentials_basis, Etale.of_comp,
Etale.etale_comp, residueFieldIsoBase, SpecMap_residueFieldIsoBase_inv, and
IsZariskiLocalAtSource.iff_of_iSup_eq_top. The two proof-only nodes
lem-sfb-finite-type-field-point-characterization and
lem-sfb-finite-type-points-detect-open currently have no Lean record or Mathlib match,
so there is no recorded module to import for them. They are not needed to type this
statement; their future proof imports can be added by the maintainer under stage-2 rule 7.
The theorem docstring records all five proof steps, including the explicit localization
formula, inverse cotangent comparison, duality argument, coordinate selection,
etale cancellation, and finite-type-point detection.

Sources read: literature/stacks-project/morphisms.tex, lemma-etale-at-point
(Tag 02GU, especially condition 8), lemma-enough-finite-type-points (02J4), and
lemma-jacobson-finite-type-points (01TB). The item is a supporting lemma, not the
blueprint unit's own statement. No source discrepancy or statement dispute was found.

Edge cases checked mathematically: for X empty the rational tangent hypothesis is
vacuous and the conclusion follows from the empty source cover; if Y is empty,
a morphism X -> Y already forces X empty. Zero-dimensional smooth schemes have
zero tangent spaces and fit the d=0 coordinate argument. No global dimension is
fixed, so disconnected schemes of differing dimensions are covered. In characteristic p,
Frobenius of affine space of positive dimension fails the bijective tangent hypothesis,
as required; no perfectness or characteristic-zero restriction was added.
The shared universe u is the recorded Scheme and schemeTangentMap convention and
can be enlarged to contain any field and pair of schemes.

Searches for an existing statement (2026-10-24):

- msearch.py leanfinder, query: "A morphism between smooth finite type schemes over
  an algebraically closed field is etale if its tangent map is bijective at every
  rational point". Eight hits: IsEtale, Scheme.Etale, smoothness and formal-unramified
  consequences of etaleness, etale category structure and standard-smooth algebra
  criteria. None states this rational tangent criterion.
- msearch.py loogle, query: "AlgebraicGeometry.Etale, AlgebraicGeometry.schemeTangentMap".
  Zero hits; the service does not index the project name schemeTangentMap.
- msearch.py grep, query:
  `(tangent|Tangent).*(etale|Etale)|([Ee]tale).*(tangent|Tangent)`, AlgebraicGeometry.
  Zero Mathlib hits.
- Direct rg with that same pattern over lean/WeilConjectures and lean/Sheaf found
  algebra cotangent results, coordinate criteria and the different theorem
  finiteLocallyFree_etale_iff_tangentMap_injective. Its full signature and docstring
  were inspected: it assumes finite locally free f, concerns one rational point,
  and uses injectivity, so it does not duplicate this theorem. Also read the
  consumer TransverseSubgroupProductOpen, which cites this as a proof prerequisite.
- Direct rg for the item id in lean/WeilConjectures returned no hits; direct rg for
  the proposed declaration name found no existing declaration.

Validation: scompile.py compiled the module in sandbox and library modes in 1.5 s
and 1.6 s respectively, with no reported diagnostics. `autoImplicit false` ensures
all variables are explicitly bound.

## Second reading by Q84

This is an author rereading, not an independent agent review; the dispatcher forbids
starting other agents and the maintainer performs the independent delivery review.
I compared the original node and the completed signature again. The key subtlety is
that the statement uses the structural residue-field map, rather than any abstract
field isomorphism, to quantify precisely X(k). Bijectivity of the residue-linear
canonical tangent map is precisely the desired k-linear isomorphism after that
identification. Both smoothness assumptions, both finite-type conjunctions and the
commuting structure-map equality are present. The conclusion is etaleness of the
original f. Empty/disconnected and arbitrary-characteristic cases remain included.
No mismatch was found and no changes resulted from this rereading.

Additional semantic search: msearch.py leansearch, query "A morphism of smooth
schemes over an algebraically closed field with bijective tangent maps at every
rational point is etale", returned eight hits: IsEtale, Scheme.Etale, its smoothness
instance, IsSmooth recursors and formally-etale algebra lifting criteria.
None is the geometric rational tangent criterion.
