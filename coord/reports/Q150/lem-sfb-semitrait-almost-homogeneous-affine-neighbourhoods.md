## Worker report

The module `Sheaf.AlgebraicGeometry.SemitraitAlmostHomogeneousAffineNeighbourhoods`
states `AlgebraicGeometry.exists_affineOpen_of_semitrait_almostHomogeneous`, with
`by sorry`. It introduces no definitions and changes only the item's `lean` field.
All variables and the universe `u` are explicit; the module disables both forms
of automatic implicit binding.

Source checked: Anantharaman, primary scan
https://www.numdam.org/article/MSMF_1973__33__5_0.pdf,
Definition 4.0.1 (printed p.53, scan p.49) and Proposition 4.2.2 and its reduction
to 4.2.3 (printed pp.57–59, scan pp.53–55). Definition 4.0.1 uses an fppf covering
map `(g,x) ↦ (gx,x)` and a finite union of homogeneous opens; Proposition 4.2.2
gives (FA) for separated almost homogeneous spaces over a semi-trait.
Also read the current blueprint's direct-images proof (3), at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`.
The present item is an auxiliary node, not that unit's statement. No correction
or disputed statement is needed.

Clause-by-clause correspondence:

- The semi-trait is exactly `Spec (CommRingCat.of R)`. The binders `[CommRing R]`,
  `[IsDomain R]`, `[IsNoetherianRing R]`, `[IsIntegrallyClosed R]`,
  `hdim : ringKrullDim R = 1` and `hmax : Set.Finite {m : Ideal R | m.IsMaximal}`
  express respectively the commutative ring, domain, Noetherian, normal-domain,
  dimension-exactly-one and finitely-many-maximal-ideals hypotheses. In particular
  dimension zero and the zero ring are excluded exactly as the node requires.
- `G X : Over (Spec (CommRingCat.of R))` are the schemes and structure maps.
  `[GrpObj G]` gives multiplication, identity, inverse and all group laws in this
  category, without commutativity. `[ModObj G X]` is the actual internal action,
  including its identity and associativity laws. No arbitrary map replaces it.
- `[IsSeparated G.hom] [Flat G.hom] [LocallyOfFiniteType G.hom]
  [QuasiCompact G.hom]` gives exactly separated, flat and finite type for G.
  Mathlib's `IsSeparated` means its diagonal is a closed immersion.
- `[IsSeparated X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom]
  [QuasiCompact X.hom] [QuasiSeparated X.hom]` gives separated, flat and finite
  presentation for X. The last three classes are the standard full finite
  presentation condition, not merely local finite presentation. Separatedness
  also implies quasi-separatedness, so this decomposition adds no restriction.
- `(n : ℕ) (U : Fin n → X.left.Opens)` with `hcover : ⨆ j, U j = ⊤`
  expresses a finite union of opens covering X. Any finite family can be
  enumerated this way. Neither n nor any open is required to be nonempty.
- `hinvariant` is the inclusion of the inverse image of U under the second
  projection in its inverse image under the action morphism. Thus the action
  maps G × U into U. In the Cartesian slice product `(snd G X).left` is precisely
  `pullback.snd G.hom X.hom`; this is Mathlib's chosen fibre product, not a copy.
- `hhomogeneous` quantifies over every test object T over the same base and
  arbitrary sections x,y factoring through U, using their underlying ranges.
  It supplies `𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left` and, for each
  cover member, a group section g taking the restriction of x to that of y.
  `Over.mk (𝒰.f i ≫ T.hom)` is that member with its induced base structure;
  `Over.homMk (𝒰.f i) rfl` is its canonical map to T. Both type annotations
  identify this exact slice morphism. Mathlib's scalar action on hom sets is
  `lift g x ≫ ModObj.smul`, so this is exactly the local lifting condition for
  `(g,x) ↦ (gx,x)` to be surjective as an fppf sheaf morphism. A section into an
  open subscheme is equivalent to a map whose range lies in that open. By
  `hinvariant` its action again lies in that open. No global transitivity or
  merely geometric-point transitivity is substituted for the node's condition.
- `(E : Set X.left) (hE : E.Finite)` and the conclusion
  `∃ V : X.left.Opens, IsAffineOpen V ∧ E ⊆ (V : Set X.left)` are exactly (FA),
  for each arbitrary finite point set. `IsAffineOpen` means the corresponding
  open subscheme is affine.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (the latter's functoriality is not needed in the signature).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`.
  These are supplied through the Cartesian monoidal slice construction in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`,
  `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`. The hypothesis uses the recorded
  fppf precoverage directly. No fpqc hypothesis is added. The fpqc dependency
  is available through the same imported module but is not needed by the signature.
- `Mathlib.CategoryTheory.Yoneda`: `Functor.IsRepresentable`, `yoneda` and
  `Functor.RepresentableBy`. The functors of points here are represented by the
  actual Over objects; the signature spells out their sections as hom sets.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, exported through Fpqc.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, exported
  through Fpqc; its stalkwise equivalence is the recorded dependency match.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, used by the definition of IsSeparated,
  with `IsSeparated` from `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; its recorded finite-type companion is
  `AlgebraicGeometry.QuasiCompact` from Morphisms.QuasiCompact.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`.
  The node's normal-domain specialization is `[IsDomain R] [IsIntegrallyClosed R]`.
- Existing Mathlib `GrpObj`, `MonObj` and `ModObj`, from the Cartesian Grp/Mod
  modules, provide the group and action structures; no additional notion is missing.
  `ringKrullDim` is from `Mathlib.RingTheory.KrullDimension.Basic`.

Proof dependencies: import `Mathlib.AlgebraicGeometry.Noetherian` for the recorded
Mathlib match of lem-weil-pbc-finite-type-over-noetherian, and
`Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine` for
`AlgebraicGeometry.Scheme.exists_affineOpen_of_isAmple`. Read the full latter
signature and docstring. The four remaining proof dependencies currently have
no Lean records (potential-smooth-cover, dedekind-smooth-fibre-dense-affine,
connected-action-affine-saturation-ample, and integral-finite-fibre-neighbourhood-transfer),
so they cannot yet be imported. They are not statement prerequisites. All five
steps of the node's natural-language proof are present in the theorem docstring.

Edge cases checked: n=0 forces X empty by hcover; empty opens and empty fibres
have no nonempty test sections, while the empty test scheme permits the empty
fppf cover. No nonemptiness binder is used for them. E empty is allowed and the
conclusion still asks for an affine open (the empty open suffices). Generic-only
pieces remain possible: no surjectivity over the base is assumed. G is not
required commutative, affine, smooth, connected or excellent; X is not required
smooth or proper. The test schemes and the ring all use universe u, rather than
an independent smaller test universe that could make homogeneity vacuous.
Cover indices use the scheme universe, allowing the usual small refinements.

Searches performed with the prescribed msearch wrapper (Q150, this item):

- LeanSearch: "An almost homogeneous separated scheme over a semilocal Dedekind
  domain has a common affine neighbourhood for each finite subset". Eight hits:
  local_affine, single-point affine neighbourhoods, and separatedness of affine
  morphisms; none gives the assertion for an arbitrary finite point set.
- LeanFinder: "A separated flat almost homogeneous scheme over a semilocal
  Dedekind domain has an affine open containing each finite subset". Eight hits:
  affineOpenCover_X, affine cover charts, subscheme covers and affine bases;
  no almost-homogeneous semi-trait theorem.
- Loogle: `"GrpObj", "IsAffineOpen"`. Zero hits.
- Mathlib grep, AlgebraicGeometry:
  `almostHomogeneous|almost.homogeneous|finite.*subset.*affine`. Zero hits.
- rg of lean/WeilConjectures and lean/Sheaf for almostHomogeneous,
  AlmostHomogeneous and semitrait.*affine found no existing statement.
  The exact node id likewise has no match in lean/WeilConjectures. Checked the
  upstream name index for semitrait/almostHomogeneous: no match. Broader group
  scheme searches found GrpObj/Over and ModObj, which are reused here.

Validation: the initial server compile diagnosed an ambiguous Over.homMk source;
explicit source/target annotations repair it. Final scompile.py exited 0 with no
errors or warnings for both the sandbox check and actual library module check.
The delivery dry run and push also run the prescribed server preflight and compile.

## Second reading by Q150

This is the same worker's fresh clause-by-clause rereading, not a claim of an
independent agent review: the dispatcher explicitly prohibits spawning agents;
the maintainer performs the independent delivery review. Reopened the node JSON
and the complete final Lean module. Checked exact dimension one, all four group
properties, all three X properties, finite invariant covering, test-scheme fppf
local lifting, and the finite-set affine conclusion against the correspondence
above. In particular the action is ModObj, not an unconstrained morphism, and
homogeneity is local on an fppf cover, not just on points. The source/target
annotations added after elaboration change no mathematical condition. No node
statement or dependency correction and no new node were necessary.
