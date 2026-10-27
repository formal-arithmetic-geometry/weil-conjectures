## Worker report

The module `Sheaf.AlgebraicGeometry.CompleteLocalSplitTorusHomLift` states
`AlgebraicGeometry.completeLocal_splitTorus_hom_lift`, with one postponed proof.
No definition or proof is introduced. The node's statement is unchanged;
`stmt_deps` gains the already landed `def-sfb-relative-split-torus` to reuse its
canonical construction rather than duplicate the Laurent-coordinate group scheme.

Source checked: Brian Conrad, *Reductive group schemes* (2014), Corollary B.3.5,
printed pp.292--293, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
PDF pages 292--293 (zero-based 291--292). The source asserts existence and
closedness of any lift; its additional conjugacy assertion is outside this node.
The source permits arbitrary residue fields and smooth affine target groups.

Hypothesis and conclusion correspondence:

- The commutative Noetherian local ring is `(R : Type u) [CommRing R]
  [IsNoetherianRing R] [IsLocalRing R]`. Its maximal ideal is
  `IsLocalRing.maximalIdeal R`.
- Completeness of the canonical map to the inverse limit of the quotients is
  `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`, the companion notion in
  the recorded adic-completion dependency. Hausdorffness and precompleteness
  are equivalent to bijectivity of that map. Including the zero-th quotient
  in Mathlib's limit makes no difference because it is the zero ring.
- The base scheme is exactly `Spec (.of R)`. The residue field is Mathlib's
  `IsLocalRing.ResidueField R`, defined as `R ⧸ IsLocalRing.maximalIdeal R`,
  and `IsLocalRing.residue R` is the actual quotient map.
- The target with all group operations and diagrams is
  `G : Grp (Over (Spec (.of R)))`. Its structure map is `G.X.hom`.
  The smoothness, affineness and finite-presentation clauses are
  `[Smooth G.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]`. Affine morphisms are quasi-compact
  and separated, hence quasi-separated, so local finite presentation here
  is exactly finite presentation, with no omitted global finiteness condition.
  An affine scheme over the affine base is equivalently affine over that base.
- The natural number `(r : ℕ)` includes zero. The source is the landed
  `relativeSplitTorus (Spec (.of R)) r`. Its definition takes the Hopf spectrum
  of `AddMonoidAlgebra Γ(S, ⊤) (Fin r → ℤ)` and pulls back along `S.toSpecΓ`.
  For `S = Spec R`, this is precisely the displayed Laurent presentation:
  `x_i = e_(basis i)`, `y_i = e_(-basis i)`, and the inverse sends `e_m` to
  the product of positive powers of the x's and negative powers of the y's.
  These maps preserve multiplication, comultiplication, counit and antipode;
  thus this reuses the same split torus and its group law, not merely its scheme.
- Set `q = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))` for reading
  the signature (there is no extra Lean abbreviation). The given `f₀` is a
  morphism from `(Over.pullback q).mapGrp.obj (relativeSplitTorus … r)` to
  `(Over.pullback q).mapGrp.obj G`. These are exactly `T_k` and `G_k` with
  their inherited group structures. Morphisms in `Grp` preserve group operations.
- The first conjunct is `∃ f : relativeSplitTorus … r ⟶ G, …`. Its equality
  `(Over.pullback q).mapGrp.map f = f₀` is equality with the prescribed
  special-fibre homomorphism, not conjugacy, existence of an isomorphism, or
  equality after forgetting the base scheme.
- The second conjunct starts with `IsClosedImmersion f₀.hom.hom.left` and
  universally quantifies over every group homomorphism `f` with that exact
  reduction. Its conclusion is `IsClosedImmersion f.hom.hom.left`. The
  successive `.hom.hom.left` forget the bundled group/monoid and over-category
  structure to obtain the actual morphism of schemes.
- No algebraic closedness, characteristic, reductivity, commutativity or
  connectedness of the target is assumed. The source is the canonical split
  torus, not an arbitrary scheme equipped with an unspecified group structure.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its
  ideal-finite-generation characterization.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`,
  `AdicCompletion.of`, and `IsAdicComplete`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`
  (exposed transitively by the geometric statement imports).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and `Grp`,
  the recorded group-scheme convention, used over the general base scheme.
  Read also the convention docstring in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- Already landed `Sheaf.AlgebraicGeometry.RelativeSplitTorus`:
  `AlgebraicGeometry.relativeSplitTorus` (node `def-sfb-relative-split-torus`,
  added to the item's statement dependencies).
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` supplies the canonical
  group-object pullback used by that torus module and by the statement;
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs` supplies the residue map.

The stated proof dependencies are imported privately: `Mathlib.AlgebraicGeometry.Pullbacks`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, and
`Sheaf.AlgebraicGeometry.RelativeTorusMonomorphismClosed`. Smoothness, finite
presentation, spectrum and closed-immersion proof dependencies already have
public imports because the statement also uses them. The three proof-only
nodes `lem-sfb-square-zero-diagonalizable-hom-lift`,
`lem-sfb-adic-diagonalizable-hom-effectivity`, and
`lem-sfb-local-torus-subgroup-special-trivial` have no recorded Lean declaration
at this reading; there is no module to import for them yet. Their full roles
are retained in the theorem's five-step natural-language proof. They are not
missing statement prerequisites. The existing proper-base-change attachment
names only the properness half of its node, but the smoothness half is already
available in the public smoothness module; no dependency interface is needed
by the present signature from that proof-only attachment.

Edge cases checked: `r = 0` gives the trivial relative group and is allowed by
`relativeSplitTorus`; when R is already a field the residue quotient still
specifies the same special fibre and the completeness assumption holds for
the zero maximal ideal; nonreduced complete local rings and all residue
characteristics are allowed. A local ring in the standard Mathlib convention
is nontrivial, so the zero ring is not a local-ring case silently excluded.
Disconnected and noncommutative smooth affine G are allowed. If `f₀` is not
closed, the second conjunct imposes nothing, while existence is still asserted.

Searches performed with the prescribed `msearch.py Q134 <item>` wrapper:

- `leanfinder`: "A homomorphism of group schemes from a split torus to a smooth
  affine group over the residue field lifts over a complete Noetherian local
  ring". Eight hits, chiefly
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`, `exists_lift`,
  and `lift`. These lift algebra maps and do not ensure the Hopf/group laws
  or closedness of every group lift; no exact match.
- `loogle`: `"GrpObj", "lift"`. Twelve hits: group-object product-lift and
  inverse identities, not lifting across a quotient of base rings.
- `grep`: `torus|diagonalizable|GrpObj.*lift`, subdirectory `AlgebraicGeometry`.
  Zero Mathlib hits.
- `leansearch`: "Lift a split torus group scheme homomorphism from the residue
  field to a complete local ring". Eight hits: completion lifts, residue-field
  lifts and `Scheme.descResidueField`, not this group-homomorphism theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for split tori,
  diagonalizable groups and torus lifts found the general-base
  `RelativeSplitTorus.lean` construction (reused), the field-only
  `DiagonalizableGroup.lean`, and different trait/cocharacter/kernel statements.
  No theorem supplies the present existence-and-every-lift-closedness assertion.
- Exact item-id search in `lean/WeilConjectures` and declaration-name search in
  `dag/lean_names_upstream.json` found no duplicate. The node's original
  statement dependencies and their full Lean signatures/docstrings were read.

No statement correction, new definition node, dependency module, or
STATEMENT-DISPUTED finding is needed. Validation: the delivered module compiled
in both server sandbox and library modes with `scompile.py`, with no errors
or non-sorry warnings (2.3 s and 2.2 s respectively).

## Second reading by Q134

A second pass by this worker compared the unchanged node and the final Lean
signature. This is a self-check; the maintainer supplies the independent review
specified by the dispatch brief. The ring, maximal ideal and completeness
hypotheses match; the bundled target carries all group diagrams; affineness
supplies the quasi-compact/quasi-separated part of finite presentation.
The canonical relative torus matches the Laurent Hopf algebra including rank
zero, and the landed definition node is explicitly cited. The given homomorphism
has the actual base-changed group schemes as source and target. The first
conjunct fixes its reduction by equality; the second quantifies over all lifts,
so it does not accidentally restrict closedness to the chosen existential lift.
No extra hypothesis on G or k was found and no revision was needed in this pass.
