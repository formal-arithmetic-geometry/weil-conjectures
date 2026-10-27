## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteCommutativeCartierRepresentability` states
`AlgebraicGeometry.finite_commutative_cartier_representability`, with its proof `sorry`.
Its helper `finiteCartierCoordinates` has real data: infer affineness from the finite
structure morphism, use `HopfAction.coordinateHopfAlgebra`, and bundle the actual
ring Γ(G,⊤) as `CommHopfAlgCat`. There is no chosen unknown object or postponed
verification inside the definition. The theorem docstring follows all ten accepted
proof steps, including the gluing on affine opens inside overlaps.

Source read: Milne, Algebraic Groups (2017), PDF pp.224--226, printed pp.212--214:
construction before Lemma 11.11, Lemma 11.11 and its proof, Theorem 11.12 and its
proof, the Cartier pairing paragraph, and Examples 11.13--11.14. This agrees with
the node's full coordinate-dual construction, including infinitesimal group schemes.
The source's algebra-valued functor is extended to scheme parameters by the node's
explicit ten-step argument; the last three steps are included in the Lean docstring.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`.
- The k-scheme is `(G : Scheme.{u}) [G.Over (Spec (.of k))]`; its group structure is
  `[GrpObj (G.asOver (Spec (.of k)))]`.
- Commutativity is `[IsCommMonObj (G.asOver (Spec (.of k)))]`.
- Finiteness is `[IsFinite (G ↘ Spec (.of k))]`. Affineness is inferred inside the
  helper, so the theorem adds no affine hypothesis.
- H is definitionally the carrier of `finiteCartierCoordinates k G`, namely Γ(G,⊤),
  with the recorded canonical Hopf structure. The finite basis `(n,b)` is a witness
  in the conclusion, not a hypothesis.
- The full linear dual is `Module.Dual k (finiteCartierCoordinates k G)`. The bundled
  Hopf algebra `D` comes with the explicit linear equivalence `e` onto that full
  vector space. This is a presentation of the dual Hopf structure by transport:
  transporting D along e gives a Hopf algebra on H* itself. Conversely any Hopf
  algebra on H* yields this bundle with e the identity. This introduces no different
  coordinate-vector-space notion: the linear equivalence, and not a geometric-point
  comparison, is supplied. In particular D cannot be functions on the reduced points
  of an infinitesimal group, since those have the wrong vector-space dimension.
- Multiplication transposes Δ: `e (d*d') h = dualDistrib ... (e d ⊗ e d') (comul h)`.
- Unit transposes ε: `e 1 h = counit h`; the following algebraMap formula records
  the whole k-linear unit map, `e (algebraMap ... a) h = a * counit h`.
- Coproduct transposes multiplication: pairing `TensorProduct.map e e (comul d)`
  with `a ⊗ b'` yields `e d (a*b')`.
- Counit transposes the unit: `counit d = e d 1`.
- Antipode transposes the antipode: `e (antipode k d) h = e d (antipode k h)`.
- The finite tensor identification is rendered by `TensorProduct.dualDistrib` and
  its evaluation on pure tensors; `TensorProduct.dualDistribEquiv` from the recorded
  finite-free tensor-dual leaf shows this is the stated identification, not an
  arbitrarily chosen pairing. Finite dimensions follow from b and e.
- G^D is exactly `(hopfSpec (.of k)).obj (op D)`, whose underlying scheme is Spec D.
  Its finiteness and commutativity are explicit conjuncts `IsFinite ...X.hom` and
  `IsCommMonObj ...X`.
- Every parameter is `T : Over (Spec (.of k))`, with no affine, reduced, nonempty,
  finite-type or separated hypothesis.
- The right side is the existing `GroupSchemeCharacters.Characters`, exactly the hom-set of
  group objects from `(Over.pullback T.hom).mapGrp.obj (Grp.mk G)` to the pullback
  of the recorded `StandardGroupSchemes.multiplicative k`.
- The conclusion supplies `c T : CommGroup (Characters ... T)` and a `MulEquiv` Φ T.
  The character multiplication is fixed by the `GroupSchemeCharacters.value` equation for
  ALL characters χ,ψ and ALL scheme-valued points z; these values are pullbacks of
  the Laurent coordinate t. Thus this is the pointwise group structure, not an
  unnormalized abstract group structure.
- Naturality is the equality of character values for every `v : T' ⟶ T` and every
  `z : S ⟶ G × T'`, comparing precomposition `v ≫ f` with `(G ◁ v)` on the right.
  Taking S = G × T' and z = identity gives equality of the Laurent coordinates;
  together with the fixed projection to T' this determines the T'-group morphism.
- Canonicity is fixed by the final formula at the identity point of G × T: the
  Laurent coordinate of Φ(f) is Σ_i pr_G^*(b_i) pr_T^*(f^*(e^-1(b_i^*))). This is
  exactly the dual-basis tensor x_alpha of proof steps 5--7, extended globally.
- No perfection, characteristic, etaleness, or invertibility-of-order assumption
  occurs anywhere. The characteristic-p infinitesimal cases remain included.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (line 180).
- Mathlib.AlgebraicGeometry.Scheme: `Scheme` (42), its category/Hom (90), `Spec`
  (470), `Spec.map` (479) and Γ notation (104).
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj` (43), `Grp` (85), `Grp.ofHom` (138);
  commutative groups and `Hom.group` in Cartesian/Grp, with `Hom.commGroup` (311).
  GroupScheme/Defs was read for the recorded finite/commutative group conventions.
- Sheaf.AlgebraicGeometry.HopfCoactionLinearization:
  `HopfAction.affineCoordinateHopfAlgebra`, `HopfAction.coordinateHopfAlgebra`.
  Both construct the canonical Mathlib affine coordinate Hopf instance.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `multiplicative`, its canonical
  Laurent Hopf group instance, `affine`, `map`, `multiplication`, `identitySection`.
- Sheaf.AlgebraicGeometry.GroupSchemeCharacters:
  `GroupSchemeCharacters.Characters` and `GroupSchemeCharacters.value`, the new
  definition-only interface of `def-sfb-group-scheme-characters`. These are abbrevs
  of the existing `PointedTorsor.Characters` and `PointedTorsor.value` (original
  declarations read in full at lines 146 and 153 of PointedTorsorLineCharacterDescent).
  No dependency on the classification theorem is added to the DAG.
- Mathlib.AlgebraicGeometry.Group.Affine: `algSpec`, `hopfSpec` (178), the Spec group
  instances, and the canonical Γ Hopf instance (337); these give precisely the
  recorded `lem-sfb-hopf-spectrum-functor` interface.
- Mathlib.LinearAlgebra.Contraction: `dualDistribEquivOfBasis` (447),
  `dualDistribEquiv` (462); Dual/Lemmas `dualDistrib` and its pure-tensor formula.
- The plain imports retain the proof plan: finite-dimensional duals in Dual/Lemmas,
  tensor-Hom in Contraction, affine-target morphisms in GammaSpecAdjunction,
  and algebra tensor maps in RingTheory.TensorProduct.Maps. Other proof nodes'
  recorded declarations are already in the public imports (finite morphisms,
  pullbacks, hopfSpec, pullbackSpecIso, ΓSpec adjunction).

Edge cases checked before writing:

- The trivial group has H = k and H* = k, producing the trivial group and one
  character over every T. A finite group over a field cannot have zero-dimensional
  H, since its identity section splits the counit; the theorem imposes no spurious
  positivity restriction on its basis witness.
- T empty is allowed; both hom-sets are singletons, Γ(T) is the zero ring, and
  every normalization/naturality formula is the unique equality there.
- Constant Z/n and μ_n exchange, including characteristic dividing n.
- α_p is self-dual (Milne Example 11.14); e preserves dimension p rather than
  replacing H* by the one-dimensional ring of functions on its geometric points.
- Imperfect fields, nonreduced parameter rings, arbitrary/nonaffine T and nonaffine
  overlaps are included. Naturality quantifies over every morphism v, including
  identities, opens and arbitrary base changes.
- A zero test algebra corresponds to the empty test scheme and is included.
- All universes and variables are bound explicitly. The single scheme universe u
  is the project's standard over-category convention and does not restrict to
  finite schemes as parameters.

Searches actually run:

1. msearch leanfinder, `finite commutative group scheme Cartier dual represented by
   dual coordinate Hopf algebra`: eight hits, including abstract finite character
   duality and `GroupLike.instCommGroup`; none represents this scheme character functor.
2. msearch loogle, `HopfAlgebra, Module.Dual`: zero hits.
3. msearch grep, `CartierDual|cartierDual|dual.*Hopf|Hopf.*dual`: zero Mathlib hits.
4. msearch leansearch, `Cartier dual finite commutative group scheme represents
   characters`: eight hits on AddChar/CharacterModule; none on group schemes.
5. rg in both live source roots for Cartier/dual/Hopf variants, followed by exact
   `cartierDual|CartierDual|dualHopf|dual_hopf|HopfAlgebra.*Dual` and the item id:
   no existing representability theorem. `FiniteDualHopfModule` is a different
   coaction on H*, not the dual coordinate Hopf algebra. Exact new declaration
   names also have no Mathlib/upstream/project match.
6. `grep -rn` of this item id in WeilConjectures: no hits. `rg` on the upstream-name
   index for the new names and CartierDual: no hits.
7. Existing character helpers found by `rg` for Characters in Sheaf/AlgebraicGeometry:
   reuse GroupSchemeCharacters.Characters and value; do not introduce a second definition.

Verification: scompile.py compiled the final module in sandbox and library modes,
8.1 s and 2.8 s respectively, without errors or warnings. No local or global build.
No statement correction, dependency repair or STATEMENT-DISPUTED issue. The repair
adds the definition node described below.

## Second reading by Q16

This is a separate self-check of the file and node; no second agent was started,
as the dispatcher explicitly forbids delegation. The maintainer's independent
review remains the external second reading.

Re-read the exact node statement against the complete file: k is a field; G is
finite and commutative over k; H is Γ(G); e identifies all coordinates with the
FULL linear dual; multiplication, unit, comultiplication, counit and antipode all
have their transposed formulas, with the unit's scalar extension explicit. The
spectrum is finite and commutative. Every scheme T is admitted. The right side is
literally the already landed hom-set of T-group objects into G_m,T. The Laurent
coordinate formula normalizes the bijection, all-point evaluation fixes pointwise
multiplication, and the naturality equation handles every T' → T. Character
values determine the morphisms since G_m is affine with its specified Laurent
coordinate, while the second projection of a morphism over T is fixed.

One issue found during this reading was that an ordinary Equiv plus a multiplication
formula would encode group compatibility only indirectly. It was replaced with an
explicit `CommGroup` witness whose multiplication is pointwise and an actual
`MulEquiv`; the revised file was compiled cleanly. No hypotheses or node clauses
were changed. The helper definition was also checked: its only inferred datum is
an existing canonical Hopf instance, and it contains no `sorry` or choice.


## New nodes

`def-sfb-group-scheme-characters` owns the definition-only module
`Sheaf.AlgebraicGeometry.GroupSchemeCharacters`. Its `Characters` abbrev is the exact
existing `PointedTorsor.Characters` hom-set G_T → G_m,T of group objects over T, and
its `value` abbrev is exactly the existing `PointedTorsor.value`, pulling the Laurent
coordinate t back along z, χ, and the projection to G_m. The original constructions
are reused, not copied. Thus the module supplies a definition-node interface without
using the torsor classification theorem. Source: Milne §11c, printed pp.213--214,
definition before Theorem 11.12 and the Cartier pairing. It has no sorry and requires
only k a field, G a group scheme and arbitrary test schemes T,S. In particular no
finiteness or commutativity of G is assumed in these definitions.

The fresh msearch LeanSearch query `group scheme characters over a test scheme and
Laurent coordinate evaluation` returned eight Laurent polynomial evaluation results.
LeanFinder `group scheme homomorphisms into multiplicative group after base change`
returned eight generic base-change/group-Yoneda declarations, not this specialized
interface. Mathlib grep `Characters|characterValue|CharacterValue` in AlgebraicGeometry
returned zero hits. Direct rg in WeilConjectures/AlgebraicGeometry/GroupScheme found no
such interface; Sheaf has the exact PointedTorsor helpers, which are reused. DAG search
found no existing group-scheme-characters definition node. Whole-blueprint search
`group characters` found four unrelated character/cohomology nodes, none equivalent;
blueprint ancestor is None, consistent with the item's existing broken ancestor chain.
All actual search outputs are retained verbatim in the new node's mathlib_searches.

## Repair of returned head 59d1b694267f

1. **H2 / theorem stmt_dep:** Removed `lem-sfb-pointed-torsor-line-character-descent`
   from the sandbox item's stmt_deps. Added `def-sfb-group-scheme-characters`, with
   its own module and full definition-node metadata, searches and source. The item
   publicly imports GroupSchemeCharacters and now names only its `Characters` and
   `value` interface. These are definitional aliases of the previous helpers, so
   all mathematical formulas and every hypothesis remain identical after unfolding.
   The main node is otherwise copied from current main; only lean and the new
   definition dependency change. No unrelated node, source file or proof is changed.

Compared the retained sandbox with the immutable returned content supplied in the
return and current read-only main: main still has the original six definition deps
and no lean record. The prescribed delivery wrapper refreshes and rebases onto current
main in its private worktree. This packet materially changes the returned delivery by
adding the definition node/module and changing the consumer import and declaration
references; it is not an unchanged re-push.

Re-read the new definition clause by clause: `Characters` is precisely the T-group
hom-set, because both groups use `Over.pullback T.hom` and `mapGrp`; `value` has domain
χ and z : S → G × T and returns Γ(S,⊤), using the original composite ending in the
first projection of G_m × T. The field and each test scheme/group variable are bound
explicitly. No group finiteness, commutativity, affine/nonempty/reduced parameter
restriction is introduced. For empty S the global-section equality is still the
unique value in the zero ring. Existing normalization, pointwise multiplication and
naturality use definitionally identical values, so the maintainer's other accepted
clause checks remain valid. Both revised modules compiled cleanly with scompile.py,
including separate library-mode compilations against the private sibling overlay.
