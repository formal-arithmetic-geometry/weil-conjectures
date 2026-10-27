## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCompleteLocalMapEffectivity` states
`AlgebraicGeometry.bijective_completeLocalPointRestriction`. Its only postponed proof is
this theorem. The six auxiliary declarations construct the canonical quotient schemes,
their inclusions, section restrictions, the compatible-family subtype, and the restriction
map into that subtype. These are helpers of this node, recorded in `lean.declarations`;
their data and functorial compatibility proofs are fully specified. No new independent
notion or dependency repair is needed.

Source checked: `literature/stacks-project/formal-spaces.tex`,
`lemma-map-into-algebraic-space` (Tag 0AQH), especially its first proof equation.
The theorem docstring carries all eight steps of the node's proof, including the
complete-local scheme calculation, representable-diagonal injectivity, the finite étale
residue extension, infinitesimal lifting, algebraization, overlap verification, and fppf
descent with the final reduction compatibility.

Hypothesis and clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, using the recorded scheme definition.
- Size convention: explicit `universe u`, `A : Type u`, `S : Scheme.{u}`, and the
  recorded `AlgebraicSpace S` definition, whose underlying fppf sheaf takes values in
  `Type u` on `(Over S)ᵒᵖ`. No independent smaller test universe is introduced.
- Commutative ring A: `[CommRing A]`.
- Noetherian: `[IsNoetherianRing A]`, the recorded Mathlib definition.
- Unique maximal ideal: `[IsLocalRing A]`. Its maximal ideal is exactly
  `IsLocalRing.maximalIdeal A`; Mathlib's nontriviality requirement agrees with
  existence of a unique maximal ideal.
- The specified S-structure: `(f : Spec (.of A) ⟶ S)`, not a chosen ring map to some
  affine replacement of S.
- The canonical completion map is a ring isomorphism:
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`. This is exactly the existing
  definition node `def-weil-pbc-adically-complete-ring`, added to `stmt_deps`.
  `AdicCompletion.of_bijective_iff` in its recorded module proves equivalence with
  bijectivity of the canonical map to the completion; for rings this is equivalent
  to a ring isomorphism. Including the zeroth quotient gives only the zero ring and
  does not change the positive-power limit.
- Every algebraic space B over S: `(B : AlgebraicSpace S)` uses the recorded
  full subcategory of fppf sheaves with representable diagonal and an étale atlas.
- The source morphism set: `B.obj.obj.obj (op (Over.mk f))`. By Yoneda this is
  precisely `Mor_S(Spec A,B)`, using the sheaf presentation of algebraic spaces.
- The nth quotient, indexed here by `n : ℕ`, is the `(n+1)`st positive quotient:
  `completeLocalQuotientOver f n` is
  `Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (m ^ (n+1)))) ≫ f)`.
- The right-hand set is `CompleteLocalPointFamily f B`, a subtype of the dependent
  product of these section sets. Its defining equation is
  `∀ n, B.obj.obj.map (completeLocalQuotientTransition f n).op (b (n+1)) = b n`.
  The transition inclusion is contravariantly induced by the canonical ring quotient
  `A/m^(n+2) → A/m^(n+1)`. This is exactly consecutive compatibility, as in the node;
  compatibility for arbitrary pairs follows by iteration.
- Restriction is the actual function `completeLocalPointRestriction f B`: its nth
  coordinate is the sheaf's map on the canonical quotient inclusion. Its subtype
  certificate follows from functoriality and the ring-quotient composition identity.
- The claimed bijection is `Function.Bijective (completeLocalPointRestriction f B)`.
  No separation, finite-type, quasi-compactness, or presentation assumption on B
  appears. There is no arbitrary choice of map or substitute existence hypothesis.

Dependency interfaces used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`; full signatures and docstrings read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentable`, `IsEtale`, `IsSurjective`;
  the source was read, including the sheaf and universe parameters.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`,
  `AdicCompletion.of_bijective_iff`.
- The metatheoretic `def-weil-size-convention` has no declaration and is rendered by
  the explicit universe binders, as its record directs.
- Mathlib's `IsLocalRing.maximalIdeal`, `Ideal.Quotient.mk`,
  `Ideal.Quotient.factor`, `Ideal.pow_le_pow_right`, `Spec.map_comp`, `Over.mk`,
  `Over.homMk` and presheaf functoriality construct the helpers. The named proof
  dependencies with recorded modules are imported privately, including the
  algebraic-space fibre product, finite separable fibre points, henselian finite
  étale lifting, complete-local product decomposition, and thickening modules.
  The remaining Mathlib proof dependencies are imported by their recorded files.
  The currently unstated infinitesimal-lifting proof node has no module to import.

Edge cases checked before writing and against the final definitions:

- A field has maximal ideal zero. Every positive quotient is the field itself;
  the compatible families are constant, and restriction has the stated bijectivity.
- An Artinian local ring eventually has zero maximal-ideal powers; the tower
  stabilizes at A. Index zero in Lean represents the residue field, not A/m^0.
- The zero ring has no maximal ideal and is correctly excluded by `IsLocalRing`;
  this does not remove a case of the node's unique-maximal-ideal hypothesis.
- B may be empty or nonseparated. The empty target has no A-point and no
  residue-field point. No construction or hypothesis presupposes a target point.
- S is arbitrary, possibly nonaffine or empty. All quotient schemes have the
  specified structural morphism by composition, with no affine-base assumption.
- No characteristic or equicharacteristic condition is used. The tower has all
  positive powers, and its natural-number indexing imposes no finite bound.

Searches for an existing statement and canonical notions:

- `msearch.py ... leanfinder`: query “Maps from the spectrum of a complete
  Noetherian local ring to an algebraic space are compatible families of maps from
  its maximal ideal power quotients”. Eight hits, including `SpecToEquivOfLocalRing`,
  `IsAdicComplete.liftAlgHom`, and affine quotient lifting; no algebraic-space
  effectivity theorem or matching canonical section tower.
- `msearch.py ... loogle`: `IsAdicComplete, IsLocalRing, AlgebraicSpace`.
  Zero hits; `AlgebraicSpace` is not a Mathlib identifier.
- `msearch.py ... leansearch`: query “Morphisms from a complete local spectrum to
  an algebraic space are determined by compatible morphisms from the quotients by
  powers of the maximal ideal”. Eight hits, including `IsAdicComplete.liftAlgHom`,
  `SpecToEquivOfLocalRing`, and `Scheme.Hom.liftQuotient`; these cover affine or
  scheme targets and are not this statement.
- `msearch.py ... grep`: `AlgebraicSpace|map_into_algebraic_space|complete.*local`
  in `Geometry/AlgebraicGeometry`: zero hits.
- `rg` in the project's `WeilConjectures/` and `Sheaf/` for
  `completeLocal|complete_local|map.effectivity|lem-sfb-space-complete-local-map-effectivity`
  found unrelated complete-local algebra, duality, and torus lifting, no match.
  Further searches for compatible-point/adic-quotient constructions found coherent
  module quotient systems, not this algebraic-space-valued section system.
- A final `rg` for `completeLocal(Point|Quotient)|CompleteLocalPointFamily|` followed
  by `bijective_completeLocalPointRestriction` in Mathlib, WeilConjectures, and
  Sheaf found none of the proposed declaration names.

No statement correction and no STATEMENT-DISPUTED flag. The node's natural-language
statement is unchanged. Only `lean` and the added existing completeness-definition
statement dependency change. The withdrawn CompactObject example was checked against
its recorded upstream replacement for the current module conventions.

Validation: scompile.py compiled the file independently as a sandbox module and at
its intended library module path, with no errors or warnings apart from the permitted
postponed theorem. All variables and universes are explicit (`autoImplicit false`).

## Second reading by Q148

Second reading written by the maintainer's reviewer (the delivered section stated that no
second reading took place). The node statement, Stacks formal-spaces.tex Tag 0AQH
(lines 7010–7026: statement and first displayed equation of the proof), the recorded
dependency declarations and the delivered module were read.

Clause list and Lean:

1. Scheme S (def-pc-scheme): `{S : Scheme.{u}}`. Correct.
2. Algebraic spaces over S (def-trf-algebraic-space): `(B : AlgebraicSpace S)`, the recorded
   full subcategory of `Sheaf (Scheme.fppfTopology.over S) (Type u)` cut out by
   `IsAlgebraicSpace` (representable diagonal and étale surjective atlas). No separatedness,
   finite type or quasi-compactness is added. Correct.
3. Universes (def-weil-size-convention): one universe `u` for `S`, `A` and the sheaf values,
   which is the universe of the recorded algebraic-space definition. There is no extra restriction.
4. A is a commutative Noetherian ring with a unique maximal ideal: `[CommRing A] [IsNoetherianRing A]
   [IsLocalRing A]`. Correct; `IsLocalRing` is exactly "unique maximal ideal" (it excludes only
   the zero ring, which has no maximal ideal).
5. Specified morphism Spec A → S (def-weil-affine-spectrum): `(f : Spec (.of A) ⟶ S)`. Correct.
6. The map A → lim_{n≥1} A/m^n is an isomorphism: `[IsAdicComplete (maximalIdeal A) A]`
   (def-weil-pbc-adically-complete-ring, recorded `IsAdicComplete`; Hausdorff + precomplete is
   bijectivity of the canonical map, and a bijective ring map is a ring isomorphism). Correct, no stronger.
7. Mor_S(Spec A, B): sections `B.obj.obj.obj (op (Over.mk f))` of the fppf sheaf at the S-scheme
   (Spec A, f). This is the Yoneda identification used throughout the project for algebraic spaces. Correct.
8. Right-hand side lim_{n≥1} Mor_S(Spec A/m^n, B): `CompleteLocalPointFamily f B`, families indexed
   by n : ℕ ↦ A/m^(n+1) (so all positive powers), with structure map `Spec.map(mk) ≫ f`, and
   consecutive compatibility `b_n = b_{n+1}|` via the transition induced by `Ideal.Quotient.factor`.
   This is the node's description of the limit (consecutive compatibility implies the full limit). Correct.
9. "Restriction" is a bijection: `completeLocalPointRestriction` restricts along the explicit quotient
   maps (genuine data, with compatibility proved, no `sorry`); the conclusion is `Function.Bijective`. Correct.

Edge cases: A a field (constant tower), A Artinian (stabilizing tower), B empty, S non-affine or arbitrary,
any characteristic: all covered; nothing presupposes a point of B or an affine S.

Records: `lean.statement` is verbatim the signature in the file; the six helpers are listed in
`lean.declarations` with source and blueprint docstrings; the theorem docstring carries the eight proof
steps; the only `sorry` is the theorem proof. Added stmt_dep def-weil-pbc-adically-complete-ring is a landed
existing record (`IsAdicComplete`). All private proof-dependency imports exist in the live tree as modules.
No existing declaration found (Mathlib has `SpecToEquivOfLocalRing` and `IsAdicComplete.liftAlgHom`
for schemes/rings only; no algebraic-space statement in Mathlib, WeilConjectures or Sheaf).

No mismatch found; no Lean change.
