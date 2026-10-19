## Worker report

Prepared `lean/Sheaf/RingTheory/WeaklyEtaleTor.lean` for
`lem-weil-pbc-weak-etale-tor`. No mathematical statement correction, new DAG node,
or dependency-record repair is needed. The two assertions are separate theorems;
all eight declarations are listed in `lean.declarations`. Both theorem proofs are
`sorry`; the six definitions have actual data. No choices from postponed existence
theorems are used.

Hypotheses and clauses:

- Commutative rings and a ring map: `(A B : Type u) [CommRing A] [CommRing B]
  [Algebra A B]`. The map is `algebraMap A B`.
- Weakly etale: `[Algebra.WeaklyEtale A B]`, exactly the declaration exposed by
  `Sheaf.RingTheory.IndPrincipalZariski`. This is flatness of the base map and of
  multiplication on the diagonal tensor ring, not the stronger ind-etale condition.
- Every nonnegative homological degree: `(i : ℕ)`.
- Arbitrary modules in both arguments: the `∀ M N : ModuleCat B` families in
  `ModuleCat.DiagonalTorComparison`, instantiated at the lifted coefficient rings.
  There are no finite generation, projectivity, flatness or boundedness assumptions
  on these modules.
- Tor over the base: `ModuleCat.torOverBase A B i M N` is literally the recorded
  `CategoryTheory.Tor'` applied to restriction of both modules along `algebraMap A B`.
  `ModuleCat.torBothMap` is the composite of the recorded bifunctor's two maps.
- The diagonal ring and its canonical action: the conclusion supplies
  `action : ∀ M N, Module (B ⊗[A] B) (torOverBase A B i M N)` and requires that
  `(b₁ ⊗ₜ[A] b₂)` acts by `torBothMap` of multiplication by `b₁` on `M` and by
  `b₂` on `N`. This condition determines the action on all tensors, since pure
  tensors additively generate the tensor ring. Thus this is an explicit expression
  of the implicit coefficient action in the node, not an arbitrary-action hypothesis.
  No action is chosen by a definition. `torDiagonalModule` merely bundles the
  displayed action parameter for use within that conclusion.
- The displayed identification: the family `e M N` consists of isomorphisms in
  `ModuleCat B` from `torDiagonalTensor A B i M N (action M N)` to Tor over `B`.
  The tensor is the actual `ModuleCat.extendScalars` along
  `(Algebra.TensorProduct.lmul' A (S := B)).toRingHom`. In particular `B` is a
  diagonal-ring module through multiplication, not through either factor inclusion.
  Reversing these isomorphisms gives the displayed orientation in the node.
- Natural in both modules: for every pair of `B`-linear maps `f,g`, the final
  equality says the two composites agree on every `b ⊗ t`. These generate the
  extended module. The action characterization and functoriality imply the Tor map
  over the base is diagonal-ring linear, so this is exactly the ordinary naturality
  square, with no unspecified comparison maps.
- The final common-bound clause: `weaklyEtale_flatResolutionBound` takes arbitrary
  `d : ℕ`. Its hypothesis `hA` quantifies over every coefficient module and supplies
  a nonnegative chain complex `F` with augmentation `ε : F ⟶ M[0]`, `QuasiIso ε`,
  flat terms, and `IsZero (F.X j)` whenever `d < j`. The conclusion is precisely
  the same existence statement over `B`. Quasi-isomorphism to `M[0]` expresses
  exactness of the augmented resolution; termwise zero above `d` expresses length
  at most `d`. The bound is uniform, whereas the resolution may depend on `M`.

Universe handling: Mathlib's `ModuleCat.monoidalCategory` explicitly requires its
module and ring universes to coincide (Monoidal/Basic.lean, lines 22–24 and 299–310).
An attempted independent module universe therefore failed. The final theorems retain
independent `u v`: the original rings have universe `u`, and both are canonically
replaced by `ULift.{v}` rings in universe `max u v` for the Tor and resolution
expressions. The algebra on the two lifted rings is the explicit `ULift.algebra'`,
built from the original algebra. This is the usual common-lift encoding, without an
extra universe equality or mathematical hypothesis. `ULift.ringEquiv` gives the
canonical identification with modules over the original rings; any prescribed module
size fits by choosing `v`. Weak etaleness is preserved by `Algebra.WeaklyEtale.ulift_iff`.
No theorem assumes a second arbitrary algebra structure on the lifted rings.

Dependency declarations read and used:

- `Sheaf.RingTheory.IndPrincipalZariski`: public exposure of `Algebra.WeaklyEtale`
  (defined in `Mathlib.RingTheory.Etale.Weakly`). The principal ind-Zariski definition
  and ind-etale clause of that node are not hypotheses of this lemma.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`, including its full
  bifunctor definition and first-variable derivation convention.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`: `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, and functorial tensor maps.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`; and
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`. The first is already part of the
  weakly-etale diagonal hypothesis; the latter states flatness of resolution terms.
- The stated proof interfaces are imported, including
  `Sheaf.Algebra.Homology.FlatResolutionTorComparison`,
  `Sheaf.Algebra.Homology.DoubleComplexCokernelHomologyIso`,
  `Sheaf.Algebra.Category.ModuleCat.TorSymmetry`, and
  `Sheaf.Algebra.FlatTorIdealCriterion`, together with the recorded Mathlib proof
  dependency modules for free modules, tensor exactness, resolution lifts, homology,
  and maps on derived functors. No dependency is restated.

Edge cases checked: degree `i=0` is included (ordinary tensor); zero modules and zero
rings are permitted; no nontriviality hypotheses occur. For `d=0`, the augmented
complex may have only its degree-zero flat term, which is isomorphic to the given
module, so the conclusion says every `B`-module is flat. There is no finite-rank or
finite-generation restriction. All naturality maps, including zero and identity
maps, are quantified. Arbitrarily large module carriers use the common lift described
above. Flatness of both maps is needed in the source proof; neither has been dropped.

Searches made:

- `msearch.py ... leanfinder`: "For a weakly etale ring map A to B the Tor groups
  of B modules are obtained from Tor over A by tensoring over B tensor A B with B".
  Eight results concern etale base change and Kahler differentials; none states this
  Tor comparison or the common flat-resolution bound.
- `msearch.py ... loogle`: `CategoryTheory.Tor, Module.Flat`. No hits.
- `msearch.py ... grep`: `WeaklyEtale|weakly.etale|flat.*diagonal`.
  Fifteen hits identify the existing weakly-etale definitions and geometric-site
  material, with no Tor comparison.
- `msearch.py ... leansearch`: "Tor comparison for weakly etale ring maps with flat
  diagonal". Service unavailable (Internal Server Error); no mathematical verdict
  is inferred from that service failure.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for weakly-etale/Tor
  combinations, this node ID, and Tor actions found no existing statement. The
  specialized first-Tor coefficient action in `TorOneSurjectiveFlatMiddle` handles
  only degree one with an algebra as its second argument; it does not supply this
  two-module action or theorem. It was read rather than copied.
- DAG searches for flat resolutions, flat dimension and two-factor actions found the
  already recorded general flat-resolution comparison, which is imported. No
  unrecorded genuine prerequisite carrying the required comparison was found.
- Exact-name search in Mathlib, upstream, `lean/Sheaf` and `dag/lean_names_upstream.json`
  found no collisions for any declaration added here.

Source checked: the complete blueprint markdown named by the node, including the
free-resolution proof and the concluding flat-dimension argument. The theorem
docstrings carry the expanded seven-step node proof, including the syzygy argument
and `d=0`. No `STATEMENT-DISPUTED` issue was found.

Validation: server-only `scompile.py`, nice 19, two threads, 60 seconds per file.
The final module compiles cleanly with no errors or warnings.
`deliver2.py NX lem-weil-pbc-weak-etale-tor --no-push` printed OK: compilation and
preflight pass, apart from the independent second reading that the next worker writes.
Nothing was pushed.

## Second reading by NX

Read independently against the complete blueprint source named by the node and
its seven expanded proof steps. Also read Stacks algebra.tex, section-tor
(Tag 00LY), definition-flat (00HB), lemma-characterize-flat (00M5), and
more-algebra.tex, lemma-tor-dimension (066F). These sources use commutative
rings, arbitrary modules and nonnegative degrees; they impose no Noetherian,
finite generation, characteristic or nonzero-ring assumption here.

Item-by-item object, hypothesis and conclusion audit (H3):

1. Objects: commutative rings A, B and a ring map A to B. Both theorems bind
   `(A B : Type u) [CommRing A] [CommRing B] [Algebra A B]`.
   The chosen map is `algebraMap A B`; every unital ring map determines such
   an algebra. Verdict: exact. Rings initially in different universes can be
   regarded in a common larger universe; no equal-size mathematical condition
   is imposed.
2. Hypothesis: the map is weakly etale. Both theorems use
   `[Algebra.WeaklyEtale A B]`. Opened the recorded dependency module
   `Sheaf.RingTheory.IndPrincipalZariski` and the defining Mathlib module
   `Mathlib.RingTheory.Etale.Weakly`: its fields are base flatness and flatness
   of `Algebra.TensorProduct.lmul'`. It does not require ind-etaleness or finite
   presentation. Verdict: exact, with both required flatness conditions.
3. Objects: arbitrary B-modules M,N and every degree i >= 0.
   `exists_weaklyEtale_tor_iso` binds `i : ℕ`; unfolding
   `DiagonalTorComparison` quantifies over all `M N : ModuleCat B`, with no
   projectivity, flatness, generation or boundedness assumptions.
   Verdict: exact. The action is chosen simultaneously for the whole module
   pair family, which permits the required naturality.
4. Object: Tor over A of the underlying modules. `torOverBase` uses the
   dependency's `CategoryTheory.Tor'` after `restrictScalars (algebraMap A B)`
   in both arguments. Read Tor.lean: Tor' derives tensor in its first argument,
   as the node specifies. `torBothMap` composes the maps of this same bifunctor
   in the two arguments. Verdict: exact; no replacement Tor construction.
5. Object: the diagonal ring T = B tensor_A B and its action on base Tor.
   `DiagonalTorComparison` existentially supplies a `Module T` structure and
   prescribes the action of every pure tensor `b₁ ⊗ b₂` as Tor of the scalar
   maps on M and N. Pure tensors additively generate T, so this fixes the
   action rather than allowing an arbitrary choice. The scalar maps are
   B-linear because B is commutative. Verdict: exactly the canonical action
   in proof steps 2 and 3. No additional coefficient-action hypothesis.
6. Conclusion: natural B-module identifications between Tor over B and
   B tensor_T Tor over A. `e M N` is a `ModuleCat B` isomorphism with the
   reverse orientation, equivalently invertible to the displayed orientation.
   `torDiagonalTensor` applies `extendScalars` along the multiplication
   homomorphism `lmul'`, using `torDiagonalModule` to bundle precisely the
   characterized action. Read ChangeOfRings.lean: this is the actual tensor
   extension using the specified ring homomorphism. Verdict: exact, including
   B-linearity, not just an identification of underlying groups.
7. Clause: natural in both M and N. The final quantified equation in
   `DiagonalTorComparison` is the naturality square evaluated on each
   `torDiagonalTmul ... b t`, for every pair of maps f,g. Such tensors generate
   the extension module. Naturality of base Tor with scalar maps makes its
   two-variable maps T-linear for the characterized actions, so the equation
   is exactly naturality for the induced extension map. Verdict: exact;
   neither unspecified naturality maps nor additional assumptions occur.
8. Final conclusion: every common flat-resolution bound over A remains a
   common bound over B. `weaklyEtale_flatResolutionBound` binds arbitrary
   `d : ℕ`. Its `hA` ranges over every A-module; its conclusion ranges over
   every B-module. On both sides it requires an augmented nonnegative chain
   complex, `QuasiIso ε`, flat terms and `IsZero (F.X j)` for `d < j`.
   Quasi-isomorphism to `single₀ M` means precisely an exact augmented
   resolution, including a surjective degree-zero augmentation. Vanishing
   above d gives length at most d. Verdict: the same uniform bound, with the
   resolution allowed to depend on the module, as required by Tag 066F.

Universe and edge-case audit: read the equal-universe constraint explicitly
stated in ModuleCat/Monoidal/Basic.lean. The theorem's independent `v` lifts
both rings canonically to `ULift.{v}` in `max u v`, with the algebra explicitly
`ULift.algebra' A (ULift.{v} B)`. Read `WeaklyEtale.ulift_iff`: this is the
induced algebra and preserves weak etaleness. Restriction along the ULift ring
equivalences gives the original module categories, and arbitrary module
carriers fit by increasing v. This is an equivalent common-universe encoding,
not an extra equality assumption. Both zero modules, the zero ring, i = 0 and
d = 0 are included. At d = 0 the augmentation identifies the sole flat term
with M. No characteristic restriction appears. Empty schemes and empty index
sets are not objects of this statement; no nonempty or finite-index premise
is hidden in it. Naturality includes identity, zero and arbitrary maps.

Dependency/interface audit (H4, H12, H13): opened all four statement dependency
nodes and their signatures, the Tor and tensor definitions, RingHom.Flat and
Module.Flat. Also opened the delivered proof-interface modules
FlatResolutionTorComparison, DoubleComplexCokernelHomologyIso, TorSymmetry and
FlatTorIdealCriterion. Their ring/module sizes admit the common-lift use above;
none is an assumed hypothesis. The six helpers merely assemble the existing
Tor bifunctor, module structures, tensor extension and a proposition expressing
this node's own conclusion. They introduce no separate independent notion.
There are no new definition nodes, dependency repairs or statement_change to
review. No genuine missing prerequisite was found.

Independent searches: `msearch.py` leanfinder with "Tor groups of modules over
an absolutely flat homomorphism and the diagonal tensor ring" returned eight
flatness/exactness criteria, no comparison. Loogle `CategoryTheory.Tor` returned
Tor and its projective vanishing/map declarations, no matching statement.
(The preliminary quoted Tor-prime text search produced unrelated substring
hits and was not used as evidence.) `msearch.py ... grep` with
`WeaklyEtale.*Tor|Tor.*WeaklyEtale|flatResolutionBound|DiagonalTorComparison`
returned zero hits. Independently ran rg on Mathlib, upstream WeilConjectures
and project lean/Sheaf for weakly-etale Tor, diagonal Tor, torBothMap and
torOverBase; no existing comparison or helper matching these declarations was
found. Generic flat-resolution computation and Tor symmetry already have
nodes and are reused, not duplicated.

H5/H6/H8/H9: all six definitions contain actual data; both theorems have whole
proofs `by sorry`. Every declaration has the source and this blueprint ID.
The first theorem docstring follows proof steps 1--5, including two-factor
naturality, and the second follows steps 6--7, including truncation at d = 0.
All universe variables and binders are explicit. The node's lean.statement
matches the main theorem signature, modulo the signature reader's whitespace
normalization. No mathematical mismatch was found; the Lean and node were
left unchanged. This second reading adds only this audit to the report.
