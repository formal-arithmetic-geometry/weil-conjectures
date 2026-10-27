## Worker report

The delivery states lem-sfb-semiabelian-cubical-rigidification in
`Sheaf.AlgebraicGeometry.SemiabelianCubicalRigidification`. Four theorems have `sorry`
proofs; nothing is proved. The two definitions select the uniquely determined cube section
and bundle it with the supplied line and rigidification. They use the named
existence-and-uniqueness theorem, whose statement determines the entire selected datum.
No arbitrary isomorphism, extra line, or merely existing object is chosen.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- The base scheme is `{S : Scheme.{u}}`, with arbitrary universe `u`.
  `G : Over S` supplies the actual scheme `G.left` and structure morphism `G.hom`.
  `[CommGrpObj G]` supplies the identity `η[G]`, inverse, multiplication, associativity,
  unit, inverse and commutativity identities, all as morphisms over S.
- Smoothness is `[Smooth G.hom]`. Separatedness is `[IsSeparated G.hom]`, literally the
  closed-immersion condition on the relative diagonal in Mathlib. Finite presentation
  is `[LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]` together with separatedness:
  separated implies quasi-separated, so these are exactly finite presentation, not
  merely local finite presentation. Geometrically connected fibres are
  `[GeometricallyConnected G.hom]`.
- Alternative (a) is `IsProper G.hom`. Alternative (b) is the other branch of `hbase`:
  every stalk of S is a domain and integrally closed, and
  `HasSemiabelianGeometricFibres (Grp.mk G)`. The latter existing definition quantifies
  over every algebraically closed `k : Type u` and `Spec k ⟶ S`, with an actual
  split-torus kernel square and fppf locally surjective abelian quotient. It allows
  `r = 0`. Its `IsAbelianVariety` quotient is proper, smooth and connected; over the
  algebraically closed field this is geometrically connected. The existing split torus
  is the finite product of the existing Laurent-polynomial multiplicative group scheme.
  No generic-only, split-over-the-base, or Noetherian restriction is imposed.
- The arbitrary line is `L : G.left.Modules`, and `hL : L.IsInvertible` means Zariski
  locally free of rank one. The arbitrary rigidification is exactly
  `r : (Scheme.Modules.tensorPullback (η[G]).left).obj L ≅ 𝟙_ S.Modules`.
- Existence and uniqueness are `existsUnique_compatible`:
  `∃! τ : 𝟙_ (CubicalLine.cube G).left.Modules ≅ CubicalLine.theta G L,
  CubicalLine.Compatible τ`. `theta` is the dependency's exact eight signed factors.
  `Compatible` imposes permutation invariance, all three identity-face normalizations,
  and the four-variable cocycle. As explicitly documented in the owning dependency,
  the normalization is independent of the scale of r, since its four appearances
  cancel in pairs. Thus r is supplied without inserting a spurious dependence into
  the predicate. `canonicalSection` and `canonical` keep L and r exactly as supplied.
- `iso_preserves_cube` takes two actual cubical rigidified lines on G and a line
  isomorphism f. Its hypothesis `hr` is precisely preservation of rigidifications
  under tensor inverse image. Its conclusion says that the eight-factor map of f
  carries the first section to the second. The arbitrary compatible sections in these
  lines are the unique ones by the first theorem. No additional symmetry of f is assumed.
- `pullback_eq_canonical` takes two groups over the same S, each with the same structural
  conditions and its own disjunctive `hbase`, and any `h : G' ⟶ G` with `[IsMonHom h]`.
  The dependency's actual `L.pullback h` equals the canonical cubical line on its actual
  pulled-back module and rigidification. This is equality of the cube sections with
  unchanged line and rigidification, also encoded as equality of the bundled records.
- `baseChange_eq_canonical` takes `g : S' ⟶ S` with `[IsImmersion g]`, hence an arbitrary
  subscheme restriction (not just an open or closed restriction), the actual fibre-product
  group `CubicalLine.baseChangedGroup g G`, and the alternative for that group as well.
  Its structural instances are exactly those inherited by base change. It equates
  the termwise base change with the canonical structure on its actual line and
  rigidification. Identity subscheme restrictions and repeated restrictions are included;
  no density, nonemptiness or properness of g is imposed.

Recorded dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, and its imported
  `IsSeparated` (whose full class was read in `Morphisms/Separated.lean`).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  the normal-domain condition also uses `IsDomain`, exactly as the normal-ring node
  directs. The node itself explicitly describes normality by the scheme's local rings.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp`, `tensorPullbackSectionId`.
  The full tensor construction in the public upstream import and the normalized
  adjunction/compositor declarations were read; no private pullback is introduced.
- `Sheaf.AlgebraicGeometry.CubicalRigidifiedLine`: `CubicalLine.cube`, `thetaWord`,
  `theta`, `Compatible`, `Word.mapIso`, `CubicalRigidifiedLine`, its pullback and
  baseChange; full source read, including the frame and normalization definitions.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `HasSemiabelianGeometricFibres`, with full signature and defining body read.
  Its already-landed node `def-sfb-semiabelian-geometric-fibres` is added to stmt_deps
  to cite this shared definition explicitly; no new node or dependency repair is needed.
- Both recorded geometric proof dependencies are imported non-publicly:
  `Sheaf.AlgebraicGeometry.RelativePicardCubeFaceDetection.relative_picard_cube_face_detection`
  (declaration namespace `AlgebraicGeometry`) and
  `Sheaf.AlgebraicGeometry.RelativeGroupUnitAxisFactorization.relative_group_unit_axis_factorization`
  (same namespace). The module docstrings and full theorem signatures were read.

Source and edge-case checks:

Moret-Bailly I 2.6 remains WANTED locally. I read Lan's revised thesis online,
https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf, Proposition the project server,
printed p.188 in the current single-spaced revision (PDF page 216), and Definition
the project server, Definition the project server and its following pullback paragraph on printed p.187.
The DAG's printed p.68 reference belongs to a different typesetting. Proposition
the project server case (1) is the abelian-scheme case; case (2) is more general than the node's
semiabelian-fibre case and does not require local Noetherianity. The node's statement
is preserved, rather than enlarged to that more general theorem. Its six proof steps
are reproduced in the relevant theorem docstrings: face construction, inclusion-exclusion
normalization, axis-unit uniqueness, permutation/cocycle, isomorphism, pullback.

Checked the empty base (all quantifiers and unique trivial modules remain meaningful),
G = S (all eight factors cancel and the section is the identity), the trivial line,
rank-zero tori/abelian fibres, all characteristics including 2 and 3 (no division),
nonreduced bases in alternative (a), arbitrary normal non-Noetherian bases in (b),
identity group maps and restrictions, and iterated pullbacks. Geometric test fields
have the scheme universe u, not an unrelated smaller universe. The theorem does not
assume the base is integral or globally connected. No statement dispute or correction.

Searches actually run (2026-10-24):

- msearch leanfinder: "Every rigidified line bundle on an abelian scheme or a semiabelian
  scheme over a normal base has a unique functorial cubical structure" returned eight
  hits (braiding of schemes, Picard functor of rings, module abelian structure, group
  pullback, condensed symmetry, preadditive equivalences). None states this theorem.
- msearch loogle: `CubicalRigidifiedLine, CubicalLine.Compatible` returned no hits;
  the remote index reports CubicalRigidifiedLine unknown. This index failure is not
  interpreted as absence of the local dependency, which was opened and reused.
- msearch grep: `cubical|semiabelian` restricted to Mathlib AlgebraicGeometry returned
  zero hits. msearch leansearch: "A rigidified line bundle on a semiabelian scheme over
  a normal base admits a unique cubical structure" returned eight unrelated smoothness,
  valuative, scheme, module and pullback declarations, none the theorem.
- rg in `lean/WeilConjectures` for CubicalRigidifiedLine/cubical rigidification/semiabelian,
  and the required node-id grep: no exact theorem. Broader theorem-of-the-cube search
  found the abelian-variety field theorem and the pointed-product field theorem;
  neither includes the relative semiabelian case or canonical cubical structures.
- rg in `lean/Sheaf` found and reused the CubicalRigidifiedLine and
  SemiabelianGeometricFibres interfaces and the two geometric proof prerequisites.
  Searches for the six new full declaration names and the new module name found
  no collision. `dag/lean_names_upstream.json` contains no exact match.
- `tools/blueprint_refs.py search cubical`: zero matching blueprint nodes. No new
  definition node is created; the required notions already have recorded interfaces.

Validation: scompile.py compiled the delivered module as a sandbox and by its real
module name against the published server library; both completed in 2.6 seconds,
with no errors or non-sorry warnings. All variables and the universe are explicit;
autoImplicit and relaxedAutoImplicit are disabled. All Lean lines are at most
100 characters. Delivery dry run and push are recorded below when completed.

Delivery dry run: `deliver2.py Q30 lem-sfb-semiabelian-cubical-rigidification --no-push`
returned `OK (dry run): commit ebe60a780a2 passes the preflight and compiles; nothing pushed`.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
