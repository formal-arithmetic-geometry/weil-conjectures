## Worker report

The following first-worker account is retained for history. Its proposed correction
and its assertion of clause-by-clause agreement are superseded by the independent
second reading below. The delivery now restores the base node statement.

The module states the corrected transition-isomorphism form of the Čech gluing
lemma.  It binds a scheme `X`, an index type `I`, an indexed family of opens `U`,
an open-cover hypothesis, locally invertible modules `F i`, transition
isomorphisms `φ i j`, and the cocycle equation
`(φ i k).hom = (φ i j).hom ≫ (φ j k).hom`; the conclusion is the existence of
an invertible module `L : X.Modules`.  The proof is `sorry` as required at
stage 2.

The original units formulation was not typable: the rings of sections on
`U i ∩ U j`, `U j ∩ U k`, and `U i ∩ U k` differ, and the statement supplied no
restriction maps to a common triple overlap.  The corrected formulation is the
transition-isomorphism statement of Stacks Lemma 00AM.  The open-cover
hypothesis is `TopologicalSpace.IsOpenCover U`; local invertibility is rendered
by `∀ i, (F i).IsInvertible`; the pairwise transition and triple-overlap clauses
are rendered by `φ` and `hφ`; the conclusion is `∃ L, L.IsInvertible`.

The dependency declaration used for invertibility is
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
`AlgebraicGeometry.Scheme.Modules.IsInvertible`.  The scheme notion is the
Mathlib declaration `AlgebraicGeometry.Scheme`.

Edge cases checked: singleton index types and identity transitions satisfy the
cocycle shape; the theorem permits empty index types and arbitrary universes
`u v` (the cover hypothesis carries the relevant nonemptiness requirement).

Searches: `msearch.py leanfinder` and `loogle` for Čech gluing of invertible
modules found no declaration; grep of Mathlib AlgebraicGeometry and the source
repository found no matching theorem.  Existing invertibility is supplied by
`AlgebraicGeometry.Scheme.Modules.IsInvertible`.

## Earlier second reading (a previous round; superseded)

The node and module were read together.  The corrected node names the same
source result and the Lean signature matches each corrected hypothesis and
conclusion clause.  The original units and multiplication clauses were removed
only because their overlap-ring restriction maps were absent; this is recorded
in `statement_change` and follows Lemma 00AM's equivalent isomorphism data.

## Earlier proposed correction (withdrawn by the second reader)

The old statement asserted multiplication by units on pairwise overlaps without
introducing restriction maps to triple overlaps, so its cocycle equation was
ill-typed.  The source place is Stacks Sheaves Lemma 00AM.  Citers
`lem-sc-glue-component-line-bundles` and `lem-sc-find-globally-generated` still
use the gluing conclusion and therefore hold.


## Second reading by M1

Read the base node, sandbox node and Lean module independently, together with the
source declarations and Stacks sheaves.tex, `lemma-glue-sheaves-structures` (00AM),
the preceding `lemma-glue-sheaves` and `lemma-glue-maps` (04TN).
The literature checkout is absent on this machine; read the upstream Stacks TeX
from https://raw.githubusercontent.com/stacks/stacks-project/master/sheaves.tex
(saved as `sheaves-source.tex` in this sandbox). The source allows any topological
space, arbitrary open covering and any sheaf of rings. Its module specialization
adds no Noetherian, separatedness, characteristic or finiteness hypothesis.

Object/hypothesis/conclusion inventory and Lean correspondence:

- Scheme X: `{X : Scheme.{u}}`, the actual Mathlib Scheme declaration from
  def-pc-scheme. Verdict: exact, arbitrary scheme.
- Arbitrary indexed open cover: `{I : Type v}`, `U : I → X.Opens`, and
  `hcover : ⨆ a, U a = ⊤`. Verdict: exactly the union-cover condition.
- Trivial local rank-one modules: these are canonically the structure modules
  on the U a, rather than extra globally defined modules F a. A trivialization
  of the glued module is recorded by its inverse image `e a` of 1, with
  `IsFreeGenerator (e a)`. Verdict: equivalent chosen trivializations; the
  actual source definition checks bijectivity on EVERY subopen, not merely
  global sections on U a.
- Units g_ab on each pairwise overlap: `g : ∀ a b, Γ(X, U a ⊓ U b)ˣ`.
  Verdict: exact sections of the unit sheaf (units in the ring of sections).
- Identity transitions: `hid : ∀ a, g a a = 1`. Verdict: exact on U a ∩ U a.
- Inverse transitions: `hinv` compares `Units.map` of g_ba and the inverse of
  `Units.map` of g_ab on every W contained in U a and U b. Verdict: exact;
  comparing on every subopen is equivalent to comparing on the whole overlap,
  by functoriality of restriction, and avoids transporting between differently
  written intersections.
- Triple cocycle: `hcoc` compares g_ac with g_ab*g_bc after `Units.map` to W
  for every W contained in U a, U b, U c. Verdict: exact, equivalent to the
  equality on their triple intersection by restriction functoriality.
- Existence and invertibility: `∃ (L : X.Modules) (e : ∀ a, Γ(L, U a)),
  L.IsInvertible ∧ ...`. Verdict: exact O_X-module, using the recorded
  Scheme.Modules.IsInvertible definition (locally isomorphic to O_X); such
  a sheaf is quasi-coherent, so this matches the node's invertible notion.
- Chosen trivializations: `∀ a, IsFreeGenerator (e a)`. Verdict: exact, no
  hollow definitions and no arbitrary global substitute for the local data.
- Prescribed transitions: on U a ∩ U b, `e a| = (g a b).val • e b|`, using
  L.presheaf.map on each side. Verdict: exact. The coordinate maps psi_a
  send e_a to 1, so multiplication by g_ab carries psi_a to psi_b, precisely
  the orientation in the node's proof and the source's commutative diagram.
- Unique compatible isomorphism: for every other L' and frames e' satisfying
  the same freeness and transition equations, `∃! f : L' ≅ L,
  ∀ a, f.hom.app (U a) (e' a) = e a`. Verdict: exact uniqueness of an
  isomorphism preserving chosen trivializations, not uniqueness of the bare
  underlying module. No invertibility hypothesis on L' is needed: its free
  frames on the covering already imply it. Quantifiers place witnesses L/e
  before all comparison objects L'/e'.

Dependency reading: opened def-pc-scheme and def-sc-invertible-module and the
actual Scheme and Modules.IsInvertible declarations. Scheme is the full
locally ringed space with affine-open cover; IsInvertible locally restricts
by pullback to SheafOfModules.unit. Opened FreeGenerator.lean:100-103:
IsFreeGenerator is exactly bijectivity of multiplication on all subopens.
The source's nonempty_iso_of_isFreeGenerator at line 538 only compares two
already existing modules; it supplies neither existence with prescribed
transitions nor unique frame-preserving isomorphism, so it cannot replace
this item. No dependency module is needed.

Edge cases: arbitrary universe u for schemes and v for the cover; no finite or
nonempty index type assumptions. An empty cover forces X to be empty; its
module sheaf is uniquely the zero/trivial sheaf, all frame conditions are
vacuous, and the unique compatible isomorphism remains meaningful. Empty
members and overlaps have the zero section ring and its singleton group of
units. A zero module on a nonempty scheme cannot satisfy free-generator
bijectivity on the covering. Singleton covers reduce to a trivial module;
all units equal to 1 give the trivial bundle. No n or characteristic parameter
occurs, so there is no restriction at n=0 or on residue characteristics.

Independent searches (different wording from the first worker):
LeanFinder `invertible sheaf with prescribed transition functions on an open
covering` returned generic section-gluing and cover declarations, no theorem
of this shape. Loogle `SheafOfModules.unit` returned the canonical unit,
unitHomEquiv and free-sheaf constructors, not this statement. LeanSearch
`local free generator section trivializes a sheaf of modules` returned an
Internal Server Error (unavailable, not evidence of absence). LeanFinder
`section of an O_X module which gives an isomorphism from the structure sheaf
on an open` returned structure-sheaf/Tilde facts, no exact definition. Ripgrep
of Mathlib, WeilConjectures and lean/Sheaf for `def IsFreeGenerator`, free
generators, cocycles and gluing found the existing source IsFreeGenerator
and its comparison theorem, no exact existence/uniqueness theorem. Searched
dag/nodes and dag/lean_names_upstream.json: other nodes use generators in
statements, but no definition node carries this predicate. Hence add the
existing-declaration DAG record def-sc-local-free-generator, without a module.

Mismatches repaired: (1) F i : X.Modules replaced local objects on U i with
global objects and required global isomorphisms, far stronger than overlap
isomorphisms; removed them. (2) local triviality was weakened to invertibility;
restored canonical trivial local modules and free frames. (3) prescribed
transitions and (4) unique compatible isomorphism were missing from the
conclusion; both restored. (5) the worker's correction claimed the original
statement was ill-typed, but 'on triple overlaps' already specifies the
restrictions; restored the base statement and removed statement_change.
(6) original docstring omitted the proof details; replaced with all four
steps and cited proof dependencies. (7) added the standard license header.
Only the existing source free-generator predicate is reused; nothing proved,
no data sorry, exactly one theorem proof sorry.

Read both citers: lem-sc-glue-component-line-bundles step 3 and
lem-sc-find-globally-generated step 4 need exactly the prescribed transition
units and frames; restoring the original statement preserves both uses.
The withdrawn correction's 'holds' verdicts did not justify the delivered
Lean, whose bare existence conclusion could not support those steps.

Validation: scompile.py compiled the repaired module cleanly on the server,
with no errors or warnings. Every binder and universe is explicit; node
lean.statement copied verbatim from the final signature.

## New nodes

def-sc-local-free-generator records the already existing declaration
AlgebraicGeometry.Scheme.Modules.IsFreeGenerator in
WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator, existing: true.
It states a chosen local trivialization as multiplication by its frame,
bijective on every subopen. This is the trivial-rank-one specialization of
the local modules in Stacks 00AM, whose chosen trivializations give frames
by inverse image of 1. The three search kinds and DAG search above establish
that no DAG definition carries the notion; the source does, so no definition
is written. Its fields follow brief-stage2 §5, and the item cites its id in
stmt_deps. Read its self-contained statement against the actual source
predicate and the Stacks gluing setup: exact. No dependency modules added.
