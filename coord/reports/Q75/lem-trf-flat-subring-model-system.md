## Worker report

The module `Sheaf.RingTheory.FlatSubringModelSystem` states
`Algebra.exists_flat_subring_model_system`, with its sole theorem proof `sorry`.
Four concrete helpers construct the tensor ring at a stage, its canonical structure map,
its algebra instance, and its pure tensors. They belong to the model-system construction
of this node, rather than introducing a separate mathematical notion. Their data use
Mathlib's tensor product, inclusion homomorphism, and `RingHom.toAlgebra`; none uses sorry
or a choice of unspecified data. All variables and universes are explicitly bound.

Clause-by-clause correspondence with the unchanged node:

- The commutative rings and their ring map are `[CommRing R] [CommRing S] [Algebra R S]`.
  The map is `algebraMap R S`; quantifying its algebra structure covers every ring map.
  The hypotheses are `hfp : Algebra.FinitePresentation R S` and
  `hflat : (algebraMap R S).Flat`.
- The index set is exactly `{A : Subalgebra ℤ R // A.FG}`, ordered by inclusion.
  `A.FG` is equivalent to finite type over the integers by `Subalgebra.fg_iff_finiteType`
  and `RingHom.finiteType_algebraMap`. Every unital subring has its unique integer
  algebra structure, so this includes precisely the finitely generated integer subrings.
- The first existential supplies `i`, a ring `B : Type u`, its `Algebra i.1 B`,
  `Algebra.FinitePresentation i.1 B`, and `theta : R ⊗[i.1] B ≃ₐ[R] S`.
  This is the node's theta after canonical tensor symmetry. A finitely presented algebra
  has a presentation using finitely many variables over `i.1 : Type u`, hence a model
  in `Type u` exists even when the given `S` lives in another universe `v`.
- `jf` belongs to the same index set, and `i ≤ jf` states the eventual-flatness threshold.
- For each `a ∈ {i, jf}`, the type `{A : Subalgebra ℤ R // A.FG ∧ a.1 ≤ A}` is
  exactly the corresponding tail. `Small.{u}`, `Nonempty`, and `IsDirectedOrder` state
  its size, nonemptiness and directedness. `Nonempty (IsColimit
  (CommRingCat.subalgebraCocone R (fun A ↦ A.FG ∧ a.1 ≤ A)))` states that its
  actual inclusion cocone, with point `R`, is colimiting in commutative rings.
  `Nonempty` here asserts the existence of the universal-property witness, not a
  substitute for the colimit's construction: the diagram and all its maps are explicit
  upstream definitions.
- For every index `j` with `hij : i ≤ j`, `flatSubringModelStage i.1 j.1 hij B`
  is literally `j.1 ⊗[i.1] B`, with scalar action induced by
  `(Subalgebra.inclusion hij).toRingHom.toAlgebra`. The structure map is `t ↦ t ⊗ 1`.
  The tensor factor order is Mathlib's base-change order; its canonical commutation
  identifies it with the node's `B ⊗[i.1] j.1`. This is the same convention already
  used by the recorded module-base-change dependency. At `j = i`, the canonical
  unit isomorphism identifies this stage with `B` as the node's proof specifies.
- Every stage structure map has `.FinitePresentation`; `jf ≤ j` implies its `.Flat`.
  These assert the two properties of the actual ring maps, using the canonical
  algebra structure, not an additional existential choice of scalar action.
- `thetaStage j hij` is an `R`-algebra equivalence `R ⊗[j.1] B_j ≃ₐ[R] S`.
  Its pure-tensor formula is
  `thetaStage j hij (r ⊗ (t ⊗ b)) = theta ((t*r) ⊗ b)` with `t` included into `R`.
  This fixes compatibility with the original theta at every stage.
- The cocartesian clause quantifies every commutative target ring `T`, and every
  pair of ring maps `f : B_j →+* T`, `g : R →+* T` agreeing on `j.1`.
  It asserts a unique `h : S →+* T` factoring both maps. The specified map `B_j → S`
  is `thetaStage.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom`;
  the specified map `R → S` is the original `algebraMap R S`.
  Thus these are precisely the node's four arrows, with ring maps to arbitrary rings,
  not merely maps preserving some externally fixed algebra structure on `T`.
  `T : Type (max u v w)` admits every sufficiently large test universe without
  the vacuity defect of a test universe smaller than the source rings.
- For `i ≤ j ≤ k`, the existential `comparison` is a ring equivalence
  `k ⊗[j] B_j ≃+* B_k`. Its nested-pure-tensor formula is
  `s ⊗ (t ⊗ b) ↦ (t*s) ⊗ b`, where `t` is included into `k`.
  This determines the canonical comparison, including its `k`-algebra compatibility;
  equivalently the equivalence is a `k`-algebra isomorphism. Inserting `1` on the left
  gives the tensor-induced transition `B_j → B_k`, sending `t ⊗ b` to `t ⊗ b`.
  The final equality states its compatibility with `thetaStage j` and `thetaStage k`
  on every `z : B_j`, not only on the original generators. The pure-tensor formulas
  uniquely determine transitions and imply their identity and composition laws.

Dependency declarations read and used:

- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` (recorded
  definition) and `RingHom.FinitePresentation` (for the stage structure maps).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`; the module definition reduces
  this to `Module.Flat` for the induced algebra, as required by the recorded node.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, related to the index predicate
  as above; the index predicate uses the same `Subalgebra.FG` notion.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: the recorded `TensorProduct`,
  `TensorProduct.mk`, `LinearMap.baseChange`, and
  `TensorProduct.AlgebraTensorModule.distribBaseChange`; the stage construction uses
  the underlying tensor product and its standard scalar convention.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, and the chosen
  colimit interface. The conclusion uses the stronger explicit inclusion cocone.
- `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`: recorded tensor ring,
  inclusions, `Algebra.TensorProduct.productMap`, and `Algebra.TensorProduct.ext`.
  The model and pushout clauses use exactly these standard tensor constructions.
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`:
  `CommRingCat.subalgebraDiagram` and `CommRingCat.subalgebraCocone` supply the
  actual inclusion diagrams and cocones, with no private copies.
- Proof imports, as required by the split:
  `WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation`,
  `CommRingCat.exists_isPushout_of_finitePresentation`;
  `Mathlib.RingTheory.FiniteStability`, `Algebra.FinitePresentation.baseChange`
  (and the transitivity result in the finite-presentation module);
  `WeilConjectures.RingTheory.ColimitFlatRingMap`,
  `RingHom.exists_eventually_flat_of_colimit_flat`.
  The theorem docstring follows all five proof steps of the node with these inputs.

Sources opened: Stacks `more-morphisms.tex`, the full statements and proofs of
`lemma-Noetherian-approximation-flat-module` and `lemma-Noetherian-approximation-flat`;
current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`
`lem-trf-local-term-locality.md` and its proof. This is the algebraic approximation
input of the accepted split, not a change to the blueprint unit.

Edge cases checked before writing and again on rereading:
zero base and target rings are allowed; no `Nontrivial`, field, domain, locality,
Noetherian, injectivity, smoothness or faithful-flatness assumption is imposed.
When `R` is finite type over the integers the index has a largest element and the
same tail/colimit clauses apply. At `j = i`, tensoring with the base gives the original
model canonically. At `j = k`, the comparison is the tensor unit isomorphism;
compatibility remains the identity relation. The case `jf = i` is included.
The empty-tail case is not excluded by an unjustified hypothesis: nonemptiness
is a conclusion because the tail contains its base point. `u` and `v` are independent;
the model's universe does not force the given rings into a common universe.

Searches for an existing statement (2026-10-24):

- `msearch.py leansearch`, query "A finitely presented flat algebra has an eventually
  flat finite presentation model over finitely generated integer subrings": eight
  hits, including `RingHom.FinitePresentation`, projectivity of finitely presented
  flat modules, and presentation data. None states the system.
- `msearch.py loogle`, query `Algebra.FinitePresentation, RingHom.Flat`: no hits.
- `msearch.py leanfinder`, query "A finitely presented flat algebra descends to
  compatible eventually flat tensor models over the directed set of finitely generated
  integer subalgebras of the base ring": eight hits. Smooth descent has stronger
  hypotheses; finite-presentation base change has no descent or eventual flatness;
  faithfully flat descent concerns a different system. None is the node's statement.
- `msearch.py grep`, query `FinitePresentation.*(subalgebra|subring)|flat.*(model|stage)|model.*flat`
  in `RingTheory`: no hits returned.
- Direct `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, using
  `FiniteType.*ℤ|Subalgebra ℤ|Subring.*FG|subring.*[Cc]olimit|[Ss]ubring.*[Mm]odel|flat_subring|flatSubring`,
  found the upstream subalgebra diagrams, flat finite-presentation model theorem,
  and directed tensor-colimit theorem. Read their signatures and pertinent source:
  none packages this system over all larger finitely generated subrings. Reused
  `CommRingCat.subalgebraCocone` directly. Searching the item id found only proof-plan
  references in two consumer modules. A name-clash search for `FlatSubringModel` and
  `flat_subring_model_system` in Mathlib and both project trees found no declaration.

Validation: `scompile.py Q75 lem-trf-flat-subring-model-system` compiled the single
module in both sandbox and library modes on the live server, each in 2.4 seconds,
without errors or non-sorry warnings. No node correction, new node, unusable dependency
record, or STATEMENT-DISPUTED issue was found.

## Second reading by Q75

The dispatcher's explicit instruction prohibits starting other agents. This section
records my second direct reading with the node and Lean file open; the maintainer's
independent review remains separate.

Rechecked the ring-map hypotheses, the exact FG-subalgebra index, `i`, model `B`,
finite presentation and theta, `jf ≥ i`, and both specified tails. All appear in the
signature. The tails use the upstream inclusion cocone with point exactly `R`.
Rechecked every later stage's finite presentation and eventual flatness. The two
occurrences of `hij` in the stage ring and its scalar map specify the same canonical
inclusion, with proof irrelevance preventing any dependence on the inclusion proof.
Rechecked the R-algebra theta family and the formula on every pure tensor, including
the identity stage. Read the unique-factorization clause: it quantifies all ring maps
and fixes both restrictions, so it does not accidentally prove only an algebra-relative
pushout. Read the comparison's complete pure-tensor formula: it forces the natural
comparison and scalar compatibility, excluding arbitrary ring isomorphisms. Its last
clause compares the maps to `S` on all elements of the earlier model. Tensor symmetry
accounts uniformly for the reversed factor order in theta, stages and comparisons.
No hypothesis or conclusion was changed during this rereading. Checked all helpers:
concrete tensor data, no sorry, no arbitrary maps, no private notation, and no
file-local instances. The only sorry is the theorem corresponding to this DAG node.
