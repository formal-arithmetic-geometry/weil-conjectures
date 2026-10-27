## Worker report

The module `Sheaf.AlgebraicGeometry.SplitTorusEtaleSubgroupLift` states
`AlgebraicGeometry.splitTorus_etale_subgroup_lift`, with its sole proof `by sorry`.
There are no new definitions, dependency repairs, or statement corrections.
The item gains the already-landed `def-sfb-relative-split-torus` statement dependency,
whose exact declaration is used. All available proof dependency modules are imported
without `public`; statement dependencies are public imports.

Source checked: Brian Conrad, *Reductive group schemes* (2014),
[Proposition 3.1.6, printed pp.83–84; Proposition B.3.4, printed pp.290–292;
Corollary B.3.5, printed pp.292–293](https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf).
Proposition 3.1.6 preserves the subgroup and the residue field over an étale
neighbourhood; the fixed split-source argument in the accepted node proof preserves
the specified parametrization as well. The six proof steps are reproduced in the
theorem docstring with every named proof input.

Hypothesis and conclusion correspondence:

- A commutative ring and its spectrum: `(A : Type u) [CommRing A]`, `Spec (.of A)`.
- A point s with algebraically closed residue field: `(s : Spec (.of A))` and
  `[IsAlgClosed ((Spec (.of A)).residueField s)]`; this is the actual scheme
  residue field, not a separately chosen algebraically closed extension.
- An S-group scheme: `G : Grp (Over (Spec (.of A)))`, the bundled form of
  the dependency's `GrpObj`; multiplication, unit, inverse, and identities are data.
- Smooth, affine, finitely presented: `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[LocallyOfFinitePresentation G.X.hom]`.
  For an affine morphism, quasi-compactness and quasi-separatedness are automatic,
  so locally finite presentation is exactly finite presentation here.
- Nonnegative rank: `(r : ℕ)` includes zero.
- The specified split torus: `relativeSplitTorus (Spec (.of A)) r`, with the
  group-algebra Hopf law from the existing definition. Pulling it back to
  `Spec κ(s)` and `Spec C` gives precisely the two split tori in the statement.
  This follows the same pullback convention as the complete-local lift dependency.
- The given subgroup immersion j₀: a morphism of the two pulled-back `Grp`
  objects, hence a group homomorphism over κ(s), with
  `(hj₀ : IsClosedImmersion j₀.hom.hom.left)`.
- A commutative A-algebra C and its affine étale spectrum map: existential
  `(C : CommRingCat.{u}) (p : Spec C ⟶ Spec (.of A))`, with `Etale p`.
  A spectrum map is equivalently its unique ring map A → C (`Spec.homEquiv`),
  giving the A-algebra structure; every morphism between these affine schemes is
  affine. Thus neither an algebra nor affineness hypothesis is lost by this encoding.
- The point u and p(u)=s: existential `q : Spec κ(s) ⟶ Spec C` with
  `hq : (Spec (.of A)).fromSpecResidueField s = q ≫ p`.
  Explicitly u is `q (IsLocalRing.closedPoint κ(s))`. Evaluation of hq at this
  point gives p(u)=s by `Scheme.fromSpecResidueField_apply`.
- The equality κ(u)=κ(s) via p: `IsIso (p.residueFieldMap u)`. Its source is
  κ(p(u)), identified with κ(s) by the preceding equality. This is the actual
  residue map of p, not an arbitrary field isomorphism. Conversely the point and
  this residue isomorphism define q uniquely, so the q encoding adds no condition.
- A closed subgroup immersion over U: existential `j` in the category of group
  objects pulled back along p, with `IsClosedImmersion j.hom.hom.left`.
- The specified fibre is exactly j₀: the last equality precomposes j with the
  canonical `pullback.map` from the residue torus to the U-torus and postcomposes
  with the projection of G_U to G. It equates this to j₀ followed by G_s → G.
  Both maps are over the same Spec κ(s); the pullback universal property makes
  this equivalent to equality in G_s. The second projection is fixed throughout,
  so no equality of group laws, embedding parametrizations, or residue maps is omitted.
- No reductivity, connectedness, or henselian assumption appears.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; its full signatures and docstrings were read.
- `def-weil-algebraic-closure`: `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (the algebraically closed clause of its
  recorded Mathlib match); this node is a Mathlib leaf and needs no Lean repair.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, bundled as `CategoryTheory.Grp`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; the group-scheme interpretation in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` was also read.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-sfb-relative-split-torus`: `AlgebraicGeometry.relativeSplitTorus`,
  `Sheaf.AlgebraicGeometry.RelativeSplitTorus`. Read its construction and source
  docstring: Hopf spectrum of Γ(S)[Z^r], pulled back along S → Spec Γ(S).
- Canonical point and map APIs: `Scheme.fromSpecResidueField`,
  `Scheme.Hom.residueFieldMap`, `Mathlib.AlgebraicGeometry.ResidueField`;
  `Over.pullback`, `Functor.mapGrp`, and `Limits.pullback.map`.
- The closely related `completeLocal_splitTorus_hom_lift` in
  `Sheaf.AlgebraicGeometry.CompleteLocalSplitTorusHomLift` was read in full;
  the present statement uses its same split-source pullback convention.

Edge cases checked: r=0 is the rank-zero Hopf algebra and trivial group, not
excluded by any positivity binder. The zero ring has no spectrum point s, so
this case is vacuous for the correct reason. G need not be connected or reductive;
its identity and all group laws are present even in rank zero. No characteristic
restriction, Noetherian condition, completeness, or henselian condition is imposed
on A. All schemes and affine coordinate rings share the arbitrary universe u;
there is no smaller independent test universe or hidden size restriction.

Searches for an exact existing statement (all performed with the supplied wrapper
for this group and item on 2026-10-24):

- LeanFinder: “A closed split torus subgroup of a smooth affine group scheme fibre
  lifts to an etale neighbourhood preserving the residue field”. Eight hits,
  concerning polynomial factor lifting, fibre definitions, and residue-field
  points; no group-homomorphism lifting theorem.
- Loogle: `"GroupScheme", "Etale"`. Zero hits.
- Mathlib grep: `\b(torus|tori)\b|multiplicative.type` in AlgebraicGeometry.
  Zero hits.
- LeanSearch: “A split torus subgroup of a smooth affine group scheme special fibre
  lifts over a residually trivial etale neighbourhood”. Eight hits (ULift,
  Scheme.Etale, smooth locus, formally étale fields, and formally smooth algebra
  lifts); none preserves group laws or gives the required embedding.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `etale.*[Tt]orus|[Tt]orus.*etale`: no exact theorem; normal-torus étale splitting
  and torus quotient results are different statements. Broader split-torus search
  found the existing RelativeSplitTorus and CompleteLocalSplitTorusHomLift modules,
  which are reused. The proposed declaration name is absent from Mathlib,
  WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`.

Validation: `scompile.py Q28 lem-sfb-split-torus-etale-subgroup-lift` compiled the
module in module mode both as sandbox and library, cleanly, with no diagnostics.
An initial `descResidueField (stalkClosedPointTo q)` expression had an instance
resolution problem for the bundled residue field; using the direct residue map
of p gives precisely the node's “via p” clause and compiled without an extra helper.
No disputed mathematical statement or node fault was found.

## Second reading by Q28

Author's second pass, not an independent review; this dispatcher brief forbids
spawning agents, and the maintainer supplies the independent review. I reread the
node and final Lean signature together. The ambient object is the group over
Spec A, and both j₀ and j are group morphisms, not mere scheme maps. The source
is the fixed canonical split torus with its original basis of characters. The
point q, its composite equation, and the residue-map isomorphism jointly express
the precise residue-preserving neighbourhood; they do not replace it by a
geometric point over a larger field. The last square preserves j₀ itself rather
than allowing a torus automorphism or conjugacy. Affineness of p and the
A-algebra on C are provided by the full faithfulness of Spec, while finite
presentation of G follows from its affine and locally finitely presented
structure morphism. Rank zero and the empty base are included. All seven
original statement dependencies and the newly cited, already-landed relative
torus dependency use their actual recorded definitions. The full six-step proof
plan is in the docstring, and every proof import with a recorded module is present.
The rereading found no mismatch requiring a statement correction.
