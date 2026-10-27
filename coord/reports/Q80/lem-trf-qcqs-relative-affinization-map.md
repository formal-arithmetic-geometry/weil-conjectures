## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsRelativeAffinizationMap` states
`AlgebraicGeometry.qcqs_relative_affinization_map`. Its only postponed theorem has
proof `sorry`; no definitions, auxiliary theorems, or nodes are introduced. Only
the item's `lean` field changes. The source was read in
`literature/stacks-project/constructions.tex`, lemma-canonical-morphism (Tag 01LY),
and lemma-spec-properties (Tag 01LX), including their proofs.

Hypothesis and clause correspondence:

- Schemes X and S and their morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  The universe u is explicit and arbitrary. No finite-type hypothesis is imposed.
- Quasi-compact and quasi-separated: `[QuasiCompact f] [QuasiSeparated f]`.
- The natural O_S-algebra A = f_* O_X is literally
  `Under.mk (⟨f.c⟩ : S.sheaf ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)`.
  Its right object is the direct-image commutative ring sheaf, and its structure
  morphism is f.c, not an arbitrary algebra structure.
- Quasi-coherence of its underlying module: the first conjunct is
  `Scheme.CommAlgebraSheaf.toModule A |>.IsQuasicoherent` (written without the
  pipeline in the actual signature). This is quasi-coherence alone, not the
  finite-type conjunction also provided by the pqf-def-coherent dependency module.
- Existence of the relative spectrum and its affine structure morphism:
  `∃ (Y : Scheme.{u}) (π : Y ⟶ S), IsAffineHom π ∧ ...`.
- Its algebra isomorphism: `a : A ≅ Under.mk ⟨π.c⟩`, with the same explicit
  sheaf-morphism annotation used for π. This is an isomorphism in
  `S.CommAlgebraSheaf`, hence respects O_S-algebra structures.
- The map c and the equation π composed with c equals f:
  `(c : X ⟶ Y) (hc : c ≫ π = f)` in the existential conclusion.
- Every affine open, rather than a chosen cover:
  `∀ (U : S.Opens), IsAffineOpen U → ...`.
- X_U and Y_U are `(f ⁻¹ᵁ U).toScheme` and `(π ⁻¹ᵁ U).toScheme`.
- The chart with section map a_U is the exact arrow
  `(π ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (a.hom.right.hom.app (op U))`.
  The first local conjunct asserts `IsIso` of this arrow. This expresses the
  chart isomorphism without introducing an unrelated chosen isomorphism. It is
  precisely the chart expression in affine_morphism_relative_spec, clause (2).
- The restricted c_U is `c.resLE (π ⁻¹ᵁ U) (f ⁻¹ᵁ U) ...`.
  Its inclusion proof is derived from hc by comp_preimage; this is just the
  typing proof for restriction, not an additional hypothesis or assertion.
- The final equality is c_U followed by that SAME chart equals
  `(f ⁻¹ᵁ U).toSpecΓ`. Mathlib's `Scheme.Opens.toSpecΓ` is defined as
  `U.toScheme.toSpecΓ ≫ Spec.map U.topIso.inv`. Thus the right side is exactly
  j_{X_U} transported along A(U) = O_X(f⁻¹ U) ≅ Γ(X_U,O), not a replacement
  by an arbitrary map. Mathlib's `Scheme.toSpecΓ` is the unit of the recorded
  Gamma--Spec adjunction, i.e. the morphism corresponding to the identity.

Dependency declarations read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `Scheme`, `Scheme.Hom`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and its QuasiCompact import, `QuasiCompact` (not LocallyOfFiniteType).
- def-weil-quasi-separated-morphism:
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated, `QuasiSeparated`.
- def-weil-pbc-comm-algebra-sheaf:
  WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf,
  `Scheme.CommAlgebraSheaf`, `Scheme.CommAlgebraSheaf.toModule`.
- pqf-def-coherent: Sheaf.AlgebraicGeometry.CoherentFiniteType imports Mathlib's
  `SheafOfModules.IsQuasicoherent`, used here as the quasi-coherent clause.
  Its conjunction `Scheme.Modules.IsQuasiCoherentFiniteType` is not asserted.
- lem-weil-pbc-affine-morphism-relative-spec:
  WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec,
  `affine_morphism_relative_spec`; its clause (2) supplies exactly the realization
  and section-normalized chart expression used in this statement.
- lem-weil-pbc-morphism-into-affine-scheme:
  Mathlib.AlgebraicGeometry.GammaSpecAdjunction, `ΓSpec.adjunction`,
  `Scheme.toSpecΓ`; also `Scheme.Opens.toSpecΓ` from AffineScheme and
  `Scheme.Opens.topIso`, `Scheme.Hom.resLE` from Restrict.
- pqf-def-affine-morphism: Mathlib.AlgebraicGeometry.Morphisms.Affine,
  `IsAffineHom`, through the public relative-spectrum import.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, `Spec`, `Spec.map`.

Proof-only imports retain the node's proof plan: Modules.Tilde (`tildeSelf`,
`tildeFinsupp`, `isoTop`); QuasicoherentPushforwardQcqs
(`Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`);
AffineAlgebraLocalMaps (`affine_algebra_local_maps`); Gluing
(`Scheme.Cover.glueMorphisms`, `ι_glueMorphisms`, `hom_ext`). The theorem docstring
contains all five natural-language proof steps and their DAG dependencies.
No import cycle or unavailable prerequisite required omission.

Edge cases checked against the signatures and source:

- Empty X: its inverse images have zero section rings and empty spectra; the
  same canonical chart equation remains meaningful, with no nonemptiness binder.
- Empty S: X must be empty and the affine-open condition remains valid.
- Empty affine U and empty inverse images are permitted; no nonzero-ring or
  nonempty-open assumption appears.
- X_U may be nonaffine, and U intersect V may be nonaffine. Only U is assumed
  affine, and only Y_U has an isomorphic spectrum chart. In particular a proper
  positive-dimensional scheme over a field is not incorrectly excluded.
- For affine f, the formula specializes to the usual affine reconstruction.
- Non-noetherian schemes, non-finite-type qcqs f, arbitrary characteristic,
  and arbitrary scheme universe u are not restricted.

Searches made with the prescribed msearch.py wrapper (Q80, this item):

- LeanFinder: “A quasi compact quasi separated scheme morphism factors through
  the relative spectrum of its direct image structure algebra with canonical
  affine charts”. Eight hits: specTargetImageFactorization, normalization maps,
  spectral-map facts, and variants; none states this result.
- Loogle: `AlgebraicGeometry.Scheme.toSpecΓ`. Twelve hits, including
  Scheme.toSpecΓ, its naturality and appTop lemmas, and ΓSpec.adjunction_unit_app.
  These provide the absolute canonical map, not the relative theorem.
- grep: `relative.?[Ss]pec|[Aa]ffinization|[Aa]ffinisation`, subdirectory
  AlgebraicGeometry. Zero Mathlib hits.
- LeanSearch: “Relative affinization of a quasi compact quasi separated scheme
  morphism with affine base charts”. Eight hits, including IsAffineHom,
  IsAffine, AffineScheme, and quasi-affine facts; none states this result.
- Direct rg over lean/WeilConjectures and lean/Sheaf using
  `relative.?[Ss]pec|[Aa]ffinization|[Aa]ffinisation|qcqs_relative_affinization`,
  followed by narrower canonical/relative-affinization searches, found the
  recorded affine-relative-Spec dependency, relative gluing, normalization,
  Stein and absolute-affinization results. Their sources do not give this
  theorem for arbitrary qcqs f with its exact charts. No duplicate was found.
- `grep -rn 'lem-trf-qcqs-relative-affinization-map' lean/WeilConjectures`
  had no match. The new declaration's full name was also absent.

Validation: prescribed scompile.py compiled both the sandbox probe and the real
module cleanly. Initial probes needed explicit sheaf-category annotations on
Under.mk; those were corrected. No mathematical statement correction was needed.
No STATEMENT-DISPUTED issue or dependency repair remains.

## Second reading by Q80

This is a separate second pass by the same worker; no independent agent was
started, as the dispatcher explicitly forbids it. The maintainer supplies the
independent delivery review.

Reopened the node statement and final Lean signature. The two hypotheses are
exactly qc and qs of f. The first conjunct refers to the actual direct-image
algebra, using f.c. Y, π, a, c, and hc are conclusions, not assumptions. For each
arbitrary affine U, the chart is fixed by a_U and is asserted isomorphic; the
restricted c uses hc solely to type its source and target; the final equality
uses that chart and the absolute canonical map with topIso transport. No source
or intersection affineness is assumed. In this reading, a possible confusion
between quasi-coherence alone and the dependency's finite-type conjunction was
checked: the file explicitly uses IsQuasicoherent alone. The opposite direction
of Spec.map and the directions of a.hom and topIso.inv were checked against their
source definitions. There is no lost clause and no additional mathematical
hypothesis. No further file changes were required by this pass.
