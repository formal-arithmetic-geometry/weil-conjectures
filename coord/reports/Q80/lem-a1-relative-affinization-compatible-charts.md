## Worker report

Item: `lem-a1-relative-affinization-compatible-charts`, group Q80, stage 2.

The module `Sheaf.AlgebraicGeometry.RelativeAffinizationCompatibleCharts` states
`AlgebraicGeometry.relative_affinization_compatible_charts`. Its only proof is `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The item node changes only in `lean`.

Source checked: `literature/stacks-project/constructions.tex`, lines 694–720,
Tag 01LY, `lemma-canonical-morphism`, together with the preceding relative-spectrum
properties (01LX). This node is the local compatible-family form of that result.

Hypotheses and clauses, matched to Lean:

- Schemes Z and S and their morphism h are `{Z S : Scheme.{u}} (h : Z ⟶ S)`.
  The single arbitrary universe is the existing category-of-schemes size convention.
- Quasi-compactness and quasi-separatedness are exactly `[QuasiCompact h]` and
  `[QuasiSeparated h]`. In particular there is no locally-of-finite-type binder:
  the finite-type definition node also provides the quasi-compact notion alone.
- A = h_* O_Z with its given algebra structure is the actual object
  `Under.mk (⟨h.c⟩ : S.sheaf ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} h.base).obj Z.sheaf)`.
  The pushforward's value on U is definitionally `Z.presheaf.obj (op (h ⁻¹ᵁ U))`;
  `h.c` is precisely h sharp, not an arbitrarily quantified algebra structure.
- Quasi-coherence of A is the first conjunct, applying
  `Scheme.CommAlgebraSheaf.toModule` and `SheafOfModules.IsQuasicoherent`.
- The existential scheme Y and affine morphism pi are
  `∃ (Y : Scheme.{u}) (π : Y ⟶ S), IsAffineHom π ∧ ...`.
  This is the relative-spectrum realization interface used by
  `affine_morphism_relative_spec` (2), characterized by the algebra isomorphism
  and the prescribed affine charts; there is no arbitrary extra structure on Y.
- The algebra isomorphism is the existential `α` between the two actual Under
  objects for h and pi. Thus it is an O_S-algebra isomorphism, not just a ring-sheaf
  isomorphism forgetting the structure maps.
- Every affine base open is quantified as `U : S.affineOpens`. Its source and
  target opens are `(h ⁻¹ᵁ U.1)` and `(π ⁻¹ᵁ U.1)`.
- The chart q_U induced by alpha_U is the explicit composite
  `(π ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (α.hom.right.hom.app (op U.1))`.
  The first conjunct after alpha says this very morphism is `IsIso` for every U;
  hence it is the required chart isomorphism, rather than an unrelated chosen chart.
  `Opens.toSpecΓ` includes the canonical `topIso.inv` transport from ambient-open
  sections to open-subscheme global sections.
- The local maps are one simultaneous existential family
  `e : ∀ U : S.affineOpens, (h ⁻¹ᵁ U.1).toScheme ⟶ (π ⁻¹ᵁ U.1).toScheme`.
  They are over U by `e U ≫ (π ∣_ U.1) = h ∣_ U.1`.
- The exact identity q_U composed with e_U equals j_U is
  `e U ≫ (π ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (...) = (h ⁻¹ᵁ U.1).toSpecΓ`.
  The right side is the Gamma–Spec unit, with the same top-section identification;
  equivalently it corresponds to the identity on A(U) = Gamma(Z, h inverse image U).
- Agreement after the target open inclusions is the last conjunct. It compares
  `pullback.fst ... ≫ e U ≫ (π ⁻¹ᵁ U.1).ι` with
  `pullback.snd ... ≫ e V ≫ (π ⁻¹ᵁ V.1).ι`.
  The pullback of the two open inclusions into Z is their intersection, so this
  says exactly that the maps into Y agree on Z_U intersect Z_V.
- There is no assumption of affineness on Z_U or U intersect V, and no global
  compactness or separation hypothesis on S. Affineness is asserted only for pi
  and for its specified charts, as in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its QuasiCompact import:
  `AlgebraicGeometry.QuasiCompact`, the quasi-compact clause of
  `def-weil-finite-type-morphism`; `LocallyOfFiniteType` was read but is not assumed.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`.
- `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`:
  `Scheme.CommAlgebraSheaf` and `Scheme.CommAlgebraSheaf.toModule`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded module for
  `pqf-def-coherent`, importing Mathlib's `SheafOfModules.IsQuasicoherent`.
  Only that node's quasi-coherence clause is used; the finite-type conjunction
  `IsQuasiCoherentFiniteType` is not incorrectly imposed here.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`, also publicly
  imported by the recorded relative-Spec module.
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`:
  `affine_morphism_relative_spec`, especially its isomorphic-chart signature.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `ΓSpec.adjunction`,
  `Scheme.toSpecΓ`; `Mathlib.AlgebraicGeometry.AffineScheme`:
  `Scheme.Opens.toSpecΓ`. These implement the recorded morphism-into-affine match.

The proof-only imports retain the entire stated DAG proof plan:
`Mathlib.AlgebraicGeometry.Modules.Tilde` (`tildeSelf`, `tildeFinsupp`),
`WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`
(`Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`),
`WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps`
(`affine_algebra_local_maps`), and `Mathlib.AlgebraicGeometry.OpenImmersion`
(`IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`). The remaining proof dependencies
are already public statement imports. The theorem docstring gives all four proof
steps with these node names. No proof-import cycle is introduced.

Edge cases checked before writing:

- Empty Z, empty S, and empty affine U are allowed. No nonemptiness or nonzero-ring
  binder occurs; `toSpecΓ` and open restriction handle the zero ring and empty scheme.
- For P^1_k to Spec k the source inverse image is nonaffine. The signature still
  types because Gamma–Spec needs an arbitrary scheme, not an affine source.
- Intersections of affine base opens can be nonaffine. The overlap clause uses
  their source open-immersion pullback, with no affine or compact hypothesis.
- An arbitrary non-quasi-compact or non-quasi-separated base is admitted, e.g. the
  identity of such a base is qcqs; no property of its global underlying space is used.
- U = V and disjoint source inverse images give the usual equal restrictions and
  equality on the empty intersection, respectively; neither case is excluded.

Searches for existing statements (2026-10-22):

- `msearch.py ... leanfinder`, query "Compatible affine charts for the relative
  spectrum of the direct image structure algebra of a quasi compact quasi separated
  morphism": 8 hits, including normalization, scheme-theoretic image, quasi-affine
  absolute Gamma–Spec results, and affine transition limits; no exact statement.
- `msearch.py ... loogle`, query `"toSpecΓ"`: 12 hits, including the canonical unit
  and its naturality, but no relative-Spec compatible-family theorem.
- `msearch.py ... grep`, query `relative[Ss]pec|affini[sz]ation`, directory
  `AlgebraicGeometry`: 0 hits returned by the search service.
- `msearch.py ... leansearch`, query "A quasi compact quasi separated morphism has
  compatible local maps into the relative spectrum of its pushforward structure
  algebra": 8 hits on qcqs predicates and composition, no exact statement.
- Direct `rg -n 'relativeAffini|relative_affini|affinization|Affinization'` over both
  `lean/WeilConjectures` and `lean/Sheaf` found
  `Sheaf.AlgebraicGeometry.QcqsRelativeAffinizationMap.qcqs_relative_affinization_map`
  (the declaration itself is `AlgebraicGeometry.qcqs_relative_affinization_map`).
  Its full source was read: it quantifies a global c with the chart identities,
  rather than this node's local family and explicit overlap compatibility. It is
  related and can imply this result by restriction, but is not this exact interface.
  Its theorem is not copied, and no competing relative-Spec definition is introduced.
- Direct search for this item's id under `lean/WeilConjectures` found no declaration.
  Direct search for the chosen theorem names in Mathlib, WeilConjectures and Sheaf
  found no collision before writing.

Compilation: prescribed `scompile.py Q80 lem-a1-relative-affinization-compatible-charts`
with the delivered module passed in sandbox mode (11.6 s) and library-module mode
(15.9 s), with no errors or warnings. `autoImplicit false` is explicit.

No statement dispute or node fault was found.

## Second reading by Q80

The dispatcher brief forbids starting other agents; this is a worker self-rereading,
not a claim of an independent reviewer. The maintainer supplies the independent review.
Reopened the node statement and final Lean file and checked the correspondences above:
qcqs h only; actual direct-image algebra; quasi-coherence; existential affine pi;
O_S-algebra alpha; the alpha-induced isomorphic chart for every affine open;
local e_U over U; the canonical identity on chart rings; and agreement after inclusion
on the source intersections. In particular the order of `Spec.map` and the alpha
component is contravariant in rings and gives q_U from Y_U to Spec A(U).
The right side `Opens.toSpecΓ` has target Spec Gamma(Z, h inverse image U), so the
canonical topIso transport has not silently been dropped. The overlap pullback uses
inclusions into Z, not projections over S. No missing clause or extra hypothesis was
found, and the clean compiled statement required no correction.
