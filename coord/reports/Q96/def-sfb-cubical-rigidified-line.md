## Worker report

The single module `Sheaf.AlgebraicGeometry.CubicalRigidifiedLine` defines
`AlgebraicGeometry.CubicalRigidifiedLine`, its isomorphisms, homomorphism pullback,
and termwise base change. The node is unchanged outside `lean`. No dependency node
is repaired and no new independent notion is introduced.

Source read: the full node and all five statement-dependency statements and Lean
records; their recorded declarations/docstrings; Moret-Bailly's original remains
locally WANTED. I opened Lan's revised thesis at
https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf,
printed pp. 186–187 (PDF pages 213–214), §3.2.2, including the displays defining
D2 and D3, (the project server)–(the project server), Definition the project server, Definition the project server and the
following pullback paragraph. The source uses rigidification to suppress the
empty factor; the node retains it explicitly. The node's reviewed, explicit
symmetric normalized cocycle formulation is used without a statement correction.
I also searched the current blueprint `literature/blueprint/latest/`: there is no
existing cubical-line definition. No released repair note exists for this item.
The example Sheaf CompactObject module is now withdrawn; I read its node's
record and the replacement upstream CompactObject source as well.

Clause-by-clause rendering:

* An arbitrary scheme S is `{S : Scheme.{u}}`. The group scheme is `(G : Over S)`
  with `[CommGrpObj G]`, Mathlib's group-object operations and commutativity,
  valid over any base, with no smoothness, finite-type or separatedness restriction.
  `G.hom` is p, `(η[G]).left` is e. The operations are actual morphisms over S.
* The line L is `line : G.left.Modules`, with `invertible : line.IsInvertible`.
  This is the recorded scheme-local rank-one notion (and implies quasi-coherence).
  `rigidification` is exactly `(tensorPullback e).obj line ≅ 𝟙_ S.Modules`.
* `CubicalLine.cube G` is the chosen product of three copies of G in Over S,
  hence the threefold fibre product. `sumMap G I` is the finite product of the
  selected projections in the commutative group of generalized points. Here
  multiplicative notation denotes the source's additive group law. The empty
  product is the constant identity map e composed with the structure map.
* `thetaWord` explicitly lists the positive triple and three singleton factors,
  then the three negative pairs and negative empty factor, with the source's
  displayed parenthesization. `Word.module` uses `tensorPullback` at every factor,
  `⊗` for the existing sheaf tensor, and `Scheme.Modules.dual` for the negative
  factors. Thus `theta` is exactly the indicated Theta_3(L).
* `sectionIso` is an isomorphism `𝟙_ (cube G).left.Modules ≅ theta G line`:
  this encodes a nowhere-vanishing section, including over nonreduced schemes.
* The first conjunct of `Compatible` tests every permutation of Fin 3 and every
  triple of generalized points over every test scheme. The second conjunct tests
  each coordinate equal to the identity. The third conjunct is exactly
  tau(x,y,z) tau(x+y,w,z) = tau(y,w,z) tau(x,y+w,z), with multiplication written
  as composition of endomorphisms of the structure module, i.e. multiplication
  of scalars. It quantifies over arbitrary schemes, not only field-valued points.
* The canonical identifications in these equalities are expressed in finite local
  frames, rather than by an arbitrary isomorphism. `Frame` assigns a forward and
  backward map at every generalized point. `Frame.valid` requires them to be
  inverses only at a factor in question. `Word.framed`/`Framed` require validity
  at the eight factors of each cube in the identity. The unused entries may both
  be zero. Consequently simultaneous valid frames exist locally by taking the
  intersection of finitely many rank-one trivializing opens; there is no global
  triviality hypothesis and no vacuity from requiring all pullbacks to be free.
  Equal scheme morphisms index the same frame, so common factors really cancel.
  `Word.frameMap` evaluates positive factors with the forward frame, negative
  factors by inserting the inverse frame into the actual `dualEvaluation`, and
  tensor nodes with the existing pullback tensor comparison and unitor.
  `value` pulls back the actual section before evaluating this map. Equality of
  these values on every local-frame test is precisely equality of the original
  sections under the canonical cancellation identification. All local tests are
  universally quantified, so are independent of frame choices and glue.
* On any identity slice the four positive and four negative factors pair up
  identically. In particular the identity-line frame cancels against its dual.
  Using r for those factors gives exactly the same unit. Scaling r changes no
  normalized slice condition; keeping `rigidification` as explicit data is correct.
* `CubicalRigidifiedLine.Iso` consists of `lineIso`, its pullback preserving the
  two rigidifications, and preservation of `sectionIso` by `thetaWord.mapIso`.
  Positive factors use the isomorphism and negative factors its inverse transpose.
* `pullbackOver` performs the source's pullback term by term, even across a base
  map g. `pullbackRigidification` follows e'^*h^*L through the normalized pullback
  composition, the identity equality, g^*e^*L, g^*r and the canonical unit map.
  `pullbackSection` is (h^3)^*tau followed by the inverse of the uniquely
  frame-normalized `comparison : Theta_3(h^*L) ≅ (h^3)^*Theta_3(L)`.
  `PreservesSums` is the explicit identity and finite-coordinate-sum compatibility
  of a homomorphism across bases. No extra assumption is required of a same-base
  homomorphism: `pullback` takes `[IsMonHom h]` and uses `hom_preservesSums`.
* `baseChangedGroup g G` is literally `(Over.pullback g).obj G`, whose underlying
  scheme is `pullback G.hom g`. Its group operations are the existing pullback of
  group objects. `baseChange` uses the actual first projection (the counit of
  Over.mapPullbackAdj), its sum compatibility, and `pullbackOver`. In particular
  this gives restriction along every subscheme inclusion; the definition also
  covers arbitrary base change as required by the identity formulation.

Dependency declarations used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (imported through Dual):
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp`; every mathematical
  module pullback in the delivered definitions is this recorded tensor inverse image.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (through Limits):
  `CategoryTheory.Limits.pullback`; Mathlib's product in Over constructs these
  fibre products. `Pi.lift` and `Pi.π` implement the cube maps.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and the existing symmetric tensor
  structure. The sheaf tensor instance on scheme modules is the same localization
  construction already used by Invertible and Dual; there is no private tensor.
* Additional existing implementation API:
  `Scheme.Modules.dual`, `dualFunctor`, `dualEvaluation` from
  `WeilConjectures.AlgebraicGeometry.Modules.Dual`, and
  `boundaryPullbackTensorIso`/`boundaryPullbackPowIso` from
  `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`.
  `pullbackUnit` is only an abbreviation for the latter's degree-zero comparison.
  Group objects, homomorphisms, Over.pullback and its induced operations are Mathlib's.

The four postponed helper theorems all realize explicit clauses of this owning
DAG definition and are included in `lean.declarations`, with source/blueprint and
complete natural-language proofs: `comparison_existsUnique` constructs the
canonical comparison prescribed in the node's pullback clause;
`pullback_properties` gives the rank-one and cubical laws of that prescribed
pullback; `hom_preservesSums` and `baseChange_preservesSums` identify the source's
homomorphism/base-change maps with the coordinate-sum description. Each proof is
`sorry` as stage 2 requires. The only data chosen from a postponed existence
statement is `comparison`, chosen from an EXISTS UNIQUE theorem that fixes it on
local frames. Thus its object is uniquely determined, rather than an arbitrary
isomorphism. All other definitions have explicit data and all necessary postponed
proofs are named, rather than hidden inside definitions.

Edge checks: empty S and G are included (all local section equations are unique);
G=S with trivial group law makes all eight factors pair up and normalization
forces the unit cube section. For a trivial line with constant cube section c,
normalization forces c=1 rather than allowing arbitrary scalar rescaling. There
is no division by 2 or 3, no restriction on characteristic or nilpotents. The
empty subset in `sumMap` is included. Identity and arbitrary homomorphisms are
accepted by `pullback`; arbitrary base changes, including identity and subscheme
restriction, are accepted by `baseChange`. Arbitrary schemes and their tests use
one explicit arbitrary universe u, with no forced object/Hom universe equality
beyond the existing Scheme convention. Auto-bound implicits are disabled.
A symbolic coefficient-vector check of the eight factors verified every
permutation, all three identity slices, and equality of the two cocycle factor
multisets after cancellation.

Searches actually run with msearch.py (Q96/item):

* LeanFinder: "Cubical structure on a rigidified invertible sheaf on a commutative
  group scheme symmetric normalized cube trivialization with cocycle": eight hits,
  principally PresheafOfGroups.OneCocycle/H1 and Scheme.Pullback.cocycle, none a
  cubical line or its eight-factor construction.
* Loogle: `"Cubical", "Invertible"`: zero hits.
* Mathlib grep: `cubical|cubist|CubeStructure|CubicalStructure`: zero hits.
* LeanSearch: "Cubical rigidified invertible sheaf group scheme symmetric normalized
  cube section": eight hits, CommRing.Pic, generic sheaf sections/global-section
  naturality, and groups of sections; none defines this notion.
* Direct rg in the project's WeilConjectures and Sheaf trees for
  `cubical|cubist|Cubical|Cubist`: only unrelated cubical topology modules,
  RelativePicardCubeFaceDetection and SymmetricLinePowerProlongation mentions;
  neither gives cubical-line data. Searching the item id in WeilConjectures and
  dag/lean_names_upstream.json found no declaration. Searches of group objects,
  tensor pullback, tensor comparisons, duals and their signatures found the API
  reused above. The upstream canonical boundary tensor comparisons were reused
  rather than redeclared. The DAG rigidified-space-lines notion concerns algebraic
  spaces without a cube section and is not a duplicate of this scheme definition.

No STATEMENT-DISPUTED flag or node correction is needed.

Validation: scompile.py compiled the final module cleanly in both its sandbox
and named-module checks, 16.1 s and 11.3 s. Only the prescribed wrapper was used;
no global build and no shared-source edits or direct Git commands were run.

## Second reading by Q96

This is the dispatcher's requested worker self-check; no independent agent was
started, as the prompt prohibits it. The maintainer's independent review remains
the independent reading. With both the node and complete Lean file open, I checked
all five explicit hypotheses, the eight signs (including the empty negative
factor), all three laws, isomorphisms, and both kinds of pullback against the
mapping above. The local-frame tests need valid frames only at finitely many
factors, so do not silently demand a globally trivial line or restrict to points
of fields. I rechecked the inverse frame in the negative evaluation and the
inverse transpose in Word.mapIso. The identity-slice condition is independent of
r because equal factors cancel; r remains explicit object data and is preserved
by isomorphisms. The cocycle is the exact ordered x,y,w,z formula of the node.
The canonical comparison is uniquely normalized rather than an unconstrained
Nonempty choice. Concrete homomorphism and base-change entry points require no
supplied comparison data. During this reading I removed a duplicate implementation
of the pullback tensor comparison in favor of the existing upstream boundary
comparison, and fixed type-inference at the identity functor by binding G and G'
explicitly; the final file compiles. No statement changes were made.
