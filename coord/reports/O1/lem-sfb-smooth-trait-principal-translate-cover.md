## Worker report

The delivery states `AlgebraicGeometry.smooth_trait_principal_translate_cover` in
`Sheaf.AlgebraicGeometry.SmoothTraitPrincipalTranslateCover`. Its sole theorem has
proof `sorry`; there are no new definitions, auxiliary theorems, or new DAG nodes.
The accepted stage-1 split and all non-`lean` node fields are preserved.

The inherited BLOCKED ending concerned an attempted stage-1 re-split. The current
node has no `lean` record and appears at stage 2 in `coord/queue.tsv`. The current
`coord/brief-stage2.md` section 0 explicitly permits this stage handoff. No released
repair note exists for the item. This delivery supplies the missing Lean statement,
without reopening its reviewed split.

Source checked: [Prasad--Yu, On quasi-reductive group schemes](https://math.stanford.edu/~conrad/papers/qrg.pdf),
Proposition 3.1, printed p.5, proof after reduction to a smooth group over a strictly
henselian DVR. It introduces A, invokes BLR p.161 Lemma 6 for a principal chart
meeting the special fibre, and covers by its R-section translates together with
the generic fibre. Quasi-compactness gives the finite subcover in this node. The
node's full eleven-step reconstruction is carried in the theorem docstring. The
local source PDF was unavailable; its cited online source was opened and read.

Hypotheses and clauses, in statement order:

- The strictly henselian DVR R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [IsStrictlyHenselianLocalRing R]`. The DVR class
  includes localness, principality and the nonfield condition. The strictly
  henselian class extends the recorded henselian-local-ring class and requires
  separably closed residue field.
- The algebraically closed residue field k is the canonical
  `IsLocalRing.ResidueField R`, with `[IsAlgClosed (IsLocalRing.ResidueField R)]`.
  Choosing this canonical residue field changes no cases: any designated residue
  field is R-isomorphic to it. This is stronger than separable closedness, exactly
  as in the node, and is stated separately.
- The fraction field is arbitrary `(K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K]`. It is not replaced by an arbitrary extension field.
- The maximal-ideal generator is `(π : R)` with
  `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`. Nonzeroness and nonunitness
  follow from the DVR condition; they are not extra assumptions.
- The group scheme over S = Spec R is `(G : Over (Spec (.of R))) [GrpObj G]`.
  `G.left` is its underlying scheme and `G.hom` its structure map. `GrpObj`
  supplies the multiplication, identity, inverse, associativity, unit and inverse
  diagrams; no commutativity or connectedness is required. The monoidal unit
  `𝟙_ (Over (Spec (.of R)))` is the identity S-scheme, so its maps to G are
  exactly the sections denoted G(R).
- Smoothness and separatedness are `[Smooth G.hom] [IsSeparated G.hom]`.
  Finite type is `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the exact
  conjunction recorded by its dependency. In particular no properness or global
  affineness of G is imposed.
- Affineness of G_K is
  `[IsAffine (pullback G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))]`.
  This is the actual fibre product, with its canonical projection to G.
- A = Gamma(G,O_G) is `Γ(G.left, ⊤)`. A global principal open is
  `G.left.basicOpen f`, not a chosen arbitrary affine neighbourhood. Mathlib's
  `Scheme.mem_basicOpen_top` identifies it with the locus where the germ is a
  unit, and `IsAffineOpen` is affineness of its open subscheme.
- The existential witnesses are `f`, `n : ℕ`, `g : Fin n → (𝟙_ ... ⟶ G)` and
  `F : Fin (n+1) → Γ(G.left, ⊤)`. The conjunct `1 ≤ n` gives the node's positive
  integer. `Fin n` lists exactly its n sections, with Lean index j corresponding
  to paper index j+1. F is the family f_0,...,f_n; its data are determined by the
  following zeroth and successor equations, not left arbitrary.
- The seed's affineness is `IsAffineOpen (G.left.basicOpen f)`.
- The seed meets G_k iff there exists a point `x` of the pullback along
  `Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))` whose first projection
  belongs to `G.left.basicOpen f`. This asserts nonempty intersection with the
  scheme-theoretic special fibre, with no rational-point or lifting assumption.
- The zeroth function is specified by
  `F 0 = G.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv π)`.
  The canonical inverse of Gamma(Spec R) = R sends π to the constant section on
  S, and `G.hom.appTop` pulls it to G; this is exactly π times 1_A.
- For each j, `(toUnit G ≫ g j) * 𝟙 G` is the actual left multiplication L_g,
  using the existing group structure on morphisms to G. Here multiplication is
  not composition of endomorphisms. Its inverse is the same expression with
  `(g j)⁻¹`. Thus the successor equation
  `F j.succ = (((toUnit G ≫ (g j)⁻¹) * 𝟙 G).left.appTop) f`
  says precisely f_{j+1} = (L_{g_j}^{-1})^* f. This works over R without invoking
  the upstream `AlgebraicGeometry.GrpObj.mulLeft` interface, which assumes a
  field. No substitute action, auxiliary map, or choice principle is introduced.
- The finite cover is `(⨆ j : Fin (n + 1), G.left.basicOpen (F j)) = ⊤`.
- Every member's affineness is
  `∀ j : Fin (n+1), IsAffineOpen (G.left.basicOpen (F j))`.
- The identity G_{f_0} = G_K is the equality of the zeroth principal-open subset
  with the range of the canonical first projection from the generic-fibre
  pullback. This projection is the base change of Spec K → Spec R, an open
  immersion for a DVR, so the range carries exactly the induced open-subscheme
  structure. This is equality as open subschemes, rather than mere existence of
  an unrelated abstract isomorphism.
- The identities G_{f_{j+1}} = L_{g_j}(G_f) are the final equalities of subsets
  with `((toUnit G ≫ g j) * 𝟙 G).left '' (G.left.basicOpen f : Set G.left)`.
  Group diagrams make this morphism an automorphism with inverse translation by
  g_j^{-1}; hence its image has precisely the induced open-subscheme structure.
- There is no connectedness assumption on G or either fibre.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  with `irreducible_iff_uniformizer` checked to interpret its generator.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`; its superclass `HenselianLocalRing` is Mathlib's.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, publicly available
  through the recorded `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its public Separated import:
  `AlgebraicGeometry.IsSeparated`; no `IsProper` hypothesis is used.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `Morphisms.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`, `Scheme.Hom.appTop`, `Scheme.ΓSpecIso`, `Scheme.basicOpen`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its recorded
  scheme-base-change convention is `Limits.pullback f T.hom`, with
  `pullback.fst` and `pullback.snd`; its declaration `moduleBaseChange` describes
  module base change, not this fibre product. No interface repair is needed.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, `IsAffineOpen`.
- `Mathlib.CategoryTheory.Monoidal.Grp` and `Monoidal.Cartesian.Grp`: `GrpObj`,
  `GrpObj.Hom.group`; `MonObj.Hom.monoid` supplies the multiplication of morphisms.
  `Cartesian.Over` and the scheme-pullbacks instance supply the group-diagram
  ambient category. These are existing notions, written inline without a copy.

The stated proof dependencies are imported privately, including
`Sheaf.AlgebraicGeometry.AffineOpenBoundaryCodimensionOne` and
`Sheaf.RingTheory.HenselianSmoothAlgebraLifting`; the ring-hom smoothness interface
and reducedness are available through the imported modules. Generic Mathlib
proof inputs for flatness, Noetherianness, Jacobson spaces, prime avoidance and
Krull intersection are also imported. The three genuinely unstated proof inputs
(smooth reduced/dense pullback, the common affine neighbourhood, and qcqs
function localization) have no module to import; they are not needed to type the
current statement. No proof dependency was removed or stated again.

Edge cases checked:

- G = Spec R with the trivial group: f = 1 and one identity translate work.
- A disconnected finite constant group: f = 1 still works; no connectedness is
  hidden in `GrpObj`, the section type, or the affine-fibre hypothesis.
- Components meeting only the generic fibre are allowed and are covered by
  the zeroth member. Special-fibre points are measured in the actual pullback.
- An empty G, an empty special fibre, and the zero ring R are already excluded
  by the identity section and DVR hypotheses; no extra Nonempty assumption was
  inserted. The residue characteristic is unrestricted.
- n = 0 is correctly excluded, while n = 1 includes both zeroth and successor
  charts. The equations for F cover every index in Fin(n+1), including both
  endpoints, and impose no distinctness of sections or opens.
- A unit f is allowed; f = 0 cannot meet the special fibre. Translation uses the
  inverse section in the function pullback, and the original section in its image.
- The arbitrary fraction field K has the same universe as R and G, matching the
  project's scheme/fibre-product size convention. Every variable and universe is
  explicitly bound; no `let` binder or file-local notation occurs in the statement.

Searches made:

- `msearch.py leanfinder`, query: "Smooth separated finite type group scheme over
  a strictly henselian discrete valuation ring with affine generic fibre admits
  an affine principal open meeting the special fibre and a finite cover by its
  translates and the generic fibre". Eight hits concerned affine covers and
  transition limits, including `Scheme.affineCover`, `exists_isOpenCover_and_isAffine`
  and `affineBasisCoverOfAffine`; none constructs this principal translate cover.
- `msearch.py leansearch`, query: "A smooth separated group over a discrete
  valuation ring with affine generic fiber has an affine principal chart meeting
  the closed fiber and a finite translated principal open cover". Eight hits on
  smoothness constructors and separatedness; none states the item.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.GroupScheme, AlgebraicGeometry.IsGroupScheme, CategoryTheory.GrpObj`.
  Result: zero hits, unknown identifier `AlgebraicGeometry.GroupScheme`. Local
  source search then found the actual existing `CategoryTheory.GrpObj` interface.
- `msearch.py grep`, query:
  `principal.*translate|translate.*principal|affine.*trait|trait.*affine`, restricted
  to Mathlib AlgebraicGeometry. Result: zero hits.
- `rg` of the same concept expressions in both project roots found the smooth
  trait generic-open lemma for affine charts and related local normalization
  modules. None is the group-scheme principal translate cover. Exact item-id
  search in both project roots returned no declaration.
- Local `rg` searches for `GroupScheme`, `GrpObj`, `leftTranslation`, `leftTranslate`,
  `mulLeft`, `translation` found the existing group-object conventions and the
  field-only `GrpObj.mulLeft` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`. Its signature and body
  were read: `lift (toUnit G ≫ g) (𝟙 G) ≫ μ[G]`. The current statement uses exactly
  this morphism through the general existing multiplication on hom sets.
- Read `Scheme.basicOpen`, its germ-unit membership theorem, `IsAffineOpen`,
  `GrpObj` and `GrpObj.Hom.group` directly. No missing notion or duplicated
  definition was found, so no new node is needed.

Validation: `scompile.py O1 lem-sfb-smooth-trait-principal-translate-cover` compiled
both the sandbox and library-module views cleanly (6.0 s and 3.0 s respectively).
The first attempt exposed a nonexistent guessed localization import; it was
removed. The second exposed category inference for a point of a pullback; an
explicit `Scheme.{u}` ascription fixed it. The successful compile has no errors or
warnings. No direct compiler invocation, global build, shared-tree edit or direct
Git command was used. The dry run and delivery results follow below.

Dry run: `deliver2.py O1 lem-sfb-smooth-trait-principal-translate-cover --no-push`
printed `OK (dry run): commit a6854caa263 passes the preflight and compiles; nothing pushed`.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
