## Worker report

The module `Sheaf.AlgebraicGeometry.BlowupPreservedOpenDiagram` states
`AlgebraicGeometry.Scheme.IdealSheafData.BlowupPreservedOpenDiagram.flat_baseChange_preserved_open_diagram`.
Its only postponed proof is this named theorem. The nine auxiliary abbreviations
name the statement's fibre products, structure maps and canonical ambient projection;
they contain real data and no proofs or choices of unspecified maps. No node statement,
accepted split, or dependency interface is changed, and no new node is needed.

This is stage 2, after Q116's passing stage-1 split. The preceding worker's stale
stage-1 refusal does not apply: `coord/brief-stage2.md` section 0 expressly distinguishes
this handoff, and `coord/queue.tsv` lists this item at stage 2 without a Lean record.
No repair note or return for the item was found in the named coordination directories.

Hypotheses and objects, matched to Lean:

- The schemes X, Z, W are `{X Z W : Scheme.{u}}`, with explicit universe `u`.
- The finite-type quasi-coherent ideal is `I : X.IdealSheafData` and
  `_hI : I.ofFiniteType`. Mathlib's IdealSheafData is the affine-compatible description
  of a quasi-coherent ideal; `ofFiniteType`, defined in
  `WeilConjectures.Compactification.FiniteTypeExtension`, means that every affine
  section ideal is finitely generated. No Noetherian or quasi-compact hypothesis is added.
- The closed immersion is `(i : Z ⟶ X) [IsClosedImmersion i]`.
- The flat base change is `(v : W ⟶ X) [Flat v]`.
- U and U_W are `I.support.compl` and `(I.comap v).support.compl`, respectively.
  `Scheme.Opens.ι` supplies their open-subscheme inclusions, retaining the restricted
  structure sheaf rather than only an equality of sets.
- I_W is exactly the dependency's `I.comap v`; P and Q are `I.blowup` and
  `(I.comap v).blowup`, with the actual `blowupMap` structure morphisms.
- P_W is `pullback I.blowupMap v`; Z_W is `pullback i v`;
  T is `pullback i I.blowupMap`. `ambientMap I i` maps T to X through P,
  and `ambientBase I i v` is exactly T_W.
- `pulledAmbient I i v` is T-hat, `pulledAmbientMap I i v` is its map to W.
  `ambientProjection I i v` is p, obtained from the inverse of Mathlib's
  canonical pullback-pasting isomorphism followed by its second projection.
  The other projection p-hat is `pullback.snd (pullback.snd i v) (I.comap v).blowupMap`.
- c is the dependency's actual `I.blowupFlatBaseChange v`. Reading its full
  definition shows that its target already has order P ×_X W. Thus this is precisely
  the node's comparison after exchanging the displayed W-first convention; no extra
  exchange is applied to the already P-first upstream morphism.

Conclusions, in their order in the theorem:

1. `IsIso (I.blowupFlatBaseChange v)` and its composition with
   `pullback.snd I.blowupMap v` assert that c is invertible and is over W.
2. `(I.comap v).support.compl = v ⁻¹ᵁ I.support.compl` is equality of the opens
   defining U_W and v inverse U. These opens specify the same restricted scheme.
3. The next two `IsIso (pullback.snd ...)` clauses are the actual projections
   P ×_X U → U and Q ×_W U_W → U_W. The third is their base-changed P_W
   projection over U_W.
4. The isomorphism δ between Q ×_W U_W and P_W ×_W U_W is characterized by
   `δ.hom ≫ pullback.fst ... = pullback.fst ... ≫ c` and equality of the
   U_W projections. It is exactly the restriction of c and commutes with the
   complement structure maps, not just an unspecified isomorphism of the opens.
5. The two `IsClosedImmersion` clauses state closedness of p and p-hat.
6. The isomorphism θ has source T-hat and target T_W. Its equations fix the Z
   and W coordinates and state `θ.hom ≫ p = p-hat ≫ c`, which is precisely
   p composed with θ equals c composed with p-hat in the node's composition order.
   Together these projection equations determine θ uniquely by pullback uniqueness.
7. `sourceOpen` is T-hat ×_W U_W, `targetOpen` is (T ×_X U) ×_X W, and
   `commonOpen` is Z_W ×_W U_W. The isomorphism ε between the first two
   is constrained on its T and W projections to be the restriction of θ.
8. The isomorphisms ρhat and ρ identify these opens with the common open.
   `ε.hom ≫ ρ.hom = ρhat.hom` is their compatibility. The two equations
   for ρhat fix its projections to Z_W and U_W. The three equations for ρ
   fix its Z and W coordinates in Z_W and its U_W projection after the open
   inclusion. The inclusions are monomorphisms, so this fixes the U_W map itself.
   The projections to Z and W jointly determine the Z_W map. Thus this explicitly
   includes commutation with both projections required by the node, without a
   choice of unrelated comparison maps.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; base-change stability is available here.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, publicly
  exposed by the flat-blowup dependency.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType` and the public Mathlib/upstream
  quasi-coherence and finite-type interfaces; no private copy is introduced.
  For ideals, the existing `IdealSheafData` plus `ofFiniteType` specialization is used,
  as in the already-landed strict-transform consumer.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `Scheme.IdealSheafData.comap`, defined as the actual kernel of the base-changed
  closed-immersion projection, and `support_comap`.
- `WeilConjectures.Blowup.Gluing`:
  `Scheme.IdealSheafData.blowup` and `blowupMap`; no new blowup construction.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`:
  `pullbackRightPullbackFstIso` for p.
- `WeilConjectures.Blowup.FlatBaseChange`:
  `Scheme.IdealSheafData.blowupFlatBaseChange`, `blowupFlatBaseChangeIso`,
  `blowupFlatBaseChangeIso_hom_snd`.
- `WeilConjectures.Blowup.Complement` (proof import):
  `Scheme.IdealSheafData.isIso_blowupMap_restrict_support_compl`.
- Remaining recorded proof interfaces are supplied through the dependency imports:
  `ideal_comap_appLE` in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`,
  `Scheme.Hom.support_ker`, `IdealSheafData.coe_support_inter`,
  `IsAffineOpen.fromSpec_image_zeroLocus`, `Spec.map`,
  `isPullback_morphismRestrict`, `pullbackRestrictIsoRestrict`, and
  `IsClosedImmersion.isStableUnderBaseChange`. The theorem docstring follows all
  five accepted proof steps and names the corresponding DAG dependencies.

Sources read: `literature/stacks-project/divisors.tex`, lemma-flat-base-change-blowing-up
(Tag 0805, lines 8351 onward), and lemma-blowing-up-gives-effective-Cartier-divisor
(Tag 02OS, clause (1), lines 8383 onward). They give the cartesian blowup square and
its complement isomorphism; the remaining equations assemble their canonical
pullbacks exactly as the accepted node's proof specifies.

Edge cases checked mathematically before drafting: I = unit ideal (U = X and the
blowup is the identity), I = zero ideal (U empty and both blowups empty), X, Z or W
empty, v = identity, Z = X, and a closed subscheme disjoint from the preserved open.
The unrestricted fibre products and isomorphism types include all these cases.
No reducedness, nonemptiness, separatedness, or characteristic assumption is used.
There is no disputed statement and no source correction.

Searches actually run using `msearch.py Q156 <item>`:

- leanfinder: `Flat blowup base change preserves the open complement and ambient
  closed immersion diagram` returned eight generic flatness/immersion results,
  including `Flat.isStableUnderBaseChange`, but no blowup diagram theorem.
- loogle: `"blowup", "Flat"` returned zero hits.
- grep: `blowup|blowUp|BlowUp|strictTransform` returned six Mathlib hits, all
  tactic-complexity prose or the future application in ReesAlgebra, no construction.
- leansearch: `Flat blowup base change isomorphism identifies preserved opens and
  closed subscheme fiber products` returned eight hits about stability under base
  change and `pullbackRestrictIsoRestrict`, no theorem for this complete diagram.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `preservedOpen|preserved_open|blowup.*[Bb]ase[Cc]hange|blowupFlatBaseChange|blowup-base-change-preserved-open-diagram`
  found the upstream blowup comparison and complement APIs and strict-transform
  consumers, but none of the full statement. The upstream `FlatBaseChange` and
  landed `StrictTransformFlatBaseChange` modules were read in full: the latter
  states equality of strict-transform ideals, not the ambient/open diagram.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
