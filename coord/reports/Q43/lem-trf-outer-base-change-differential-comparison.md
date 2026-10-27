## Worker report

The new module `Sheaf.RingTheory.OuterBaseChangeDifferentialComparison` states
`KaehlerDifferential.OuterBaseChange.comparison`, with its entire proof `sorry`.
It includes all three isomorphisms and both inverse tensor formulas. No node
statement, dependency list, or proof plan changes. There are no new nodes or
dependency repairs.

Hypotheses and clauses, matched against the node:

- The four commutative rings are `A : Type uA`, `B : Type uB`, `C : Type uC`,
  `T : Type uT`, with four `CommRing` instances and independent universes.
- The three outer algebra structures are `[Algebra A B]`, `[Algebra A C]`,
  `[Algebra A T]`. The specified A-algebra homomorphism B to C is encoded by
  `[Algebra B C] [IsScalarTower A B C]`; its underlying map is `algebraMap B C`.
  This covers every A-algebra homomorphism by its `toAlgebra` structure, and the
  tower is exactly A-linearity, not an additional mathematical assumption.
- `B_T` and `C_T` are literally `T ⊗[A] B` and `T ⊗[A] C`. The exported scoped
  instance `tensorAlgebra` constructs their algebra structure by the actual map
  `Algebra.TensorProduct.map (AlgHom.id A T) (IsScalarTower.toAlgHom A B C)`.
  The first conjunct states its prescribed `t ⊗ b ↦ t ⊗ φ(b)` formula.
- `M_0` is Mathlib `KaehlerDifferential B C`; the two universal derivations are
  `KaehlerDifferential.D B C` and
  `KaehlerDifferential.D (T ⊗[A] B) (T ⊗[A] C)`.
- `q` has type `(T ⊗[A] B) ⊗[B] C ≃ₐ[T ⊗[A] B] T ⊗[A] C`.
  The next two conjuncts give exactly the forward and inverse formulas in the
  node. `AlgEquiv` includes inverse identities, multiplicativity, unit and
  compatibility with the specified B_T structure, so none is postponed as data.
- `m : Module (T ⊗[A] C) (T ⊗[A] KaehlerDifferential B C)` is a conclusion.
  The fourth conjunct fixes its action for every pure tensor, exactly
  `(t ⊗ c) • (u ⊗ ω) = tu ⊗ c • ω`. By additivity in both arguments this
  determines the action on all elements. This is an existence assertion with
  the full canonical specification, not a definition choosing unspecified data.
- `h` is a C_T-linear equivalence from `C_T ⊗[C] M_0` to `T ⊗[A] M_0`, using
  exactly the concluded module structure `m` on the latter. The fifth and sixth
  conjuncts give `h ((t ⊗ c) ⊗ ω) = t ⊗ c • ω` and
  `h.symm (t ⊗ ω) = (t ⊗ 1) ⊗ ω`. Explicit `@LinearEquiv` arguments make the
  dependence on `m` visible without a statement-local `letI` or private notation.
- `F` is a C_T-linear equivalence from `T ⊗[A] M_0`, with the same `m`, to
  `KaehlerDifferential B_T C_T`. The final conjunct is precisely
  `F (t ⊗ d_0 c) = (t ⊗ 1) • d_T (1 ⊗ c)` for all t and c.
  This specifies the transported canonical map, not an arbitrary isomorphism:
  `d_0 c` span M_0 over C, so the prescribed action implies that the elements
  `t ⊗ d_0 c` span the source over C_T. A C_T-linear map with this formula is
  therefore unique. The transport of ordinary base change by the uniquely
  specified q and h has this formula (the node's proof steps 3 and 4), and
  consequently is exactly F. The formula thus expresses the canonical clause
  without assuming an arbitrary pushout structure or introducing a second map.
- There is no finite-generation, finite-type, flatness, nontriviality, field or
  characteristic hypothesis.

Dependency declarations read and used:

- `def-weil-pbc-kahler-differentials`: public import
  `Mathlib.RingTheory.Kaehler.TensorProduct` exposes its recorded module
  `Mathlib.RingTheory.Kaehler.Basic`, with `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`, and
  `LinearMap.rTensor`, in `LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`.
  These are publicly imported transitively by the tensor and differential
  modules. The node is a Mathlib leaf with its authoritative `mathlib_match`.
- The proof dependency `lem-weil-pbc-kahler-differentials-base-change` is the
  Mathlib leaf `KaehlerDifferential.tensorKaehlerEquivBase` and its C_T-linear
  version `KaehlerDifferential.tensorKaehlerEquiv`, from the imported
  `Mathlib.RingTheory.Kaehler.TensorProduct`.
- The proof dependency `lem-weil-pbc-algebra-tensor-pushout-universal-property`
  is the Mathlib leaf `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`,
  `includeLeft`, `includeRight`, `productMap`, `productMap_apply_tmul`, `ext`.
  Their modules `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps` are public
  because the statement's scoped tensor algebra uses this same interface.
- `rightAlgebra` registers Mathlib's existing
  `Algebra.TensorProduct.rightAlgebra` as an exported scoped instance; it is
  an alias to the existing construction, not a second construction.

Sources opened: `literature/stacks-project/algebra.tex`, the full statement and
proof of `lemma-differentials-base-change` (Tag 00RV), and the statement and proof
of `lemma-colimit-unramified` (Tag 0C4F). The latter explains the scalar-extended
rings and the former proves ordinary base change with no flatness assumptions.
The theorem docstring gives the four steps of the supplied explicit comparison
proof and all their named dependencies.

Edge cases checked mathematically before finalizing: T the zero ring (both
extended rings and differential modules vanish), C the zero ring, B = C and the
identity map (differentials vanish), T = A with the identity outer map, nonflat
T (including quotient scalar extensions), arbitrary characteristic, and four
independent size universes. The statement excludes none of these. No object
universe is forced to equal another. The canonical formulas respect tensor
balancing in all of these cases.

Searches (raw msearch results are in the sandbox's `searches.jsonl`):

- msearch leanfinder: "For A algebras B and C and A algebra T identify T tensor_A
  Omega C B with Omega (T tensor_A C) (T tensor_A B) with tensor cancellation
  formulas". Eight hits, including `tensorKaehlerEquivBase`,
  `tensorKaehlerEquiv`, and their pure-differential lemmas; none states both
  outer tensor cancellations and their inverses.
- msearch loogle: "KaehlerDifferential.tensorKaehlerEquivBase,
  Algebra.TensorProduct.cancelBaseChange". Zero hits for the combined query.
- msearch grep: `tensorKaehlerEquiv|cancelBaseChange|tensor.*[Mm]odule` in
  `RingTheory/Kaehler`. Ten hits: ordinary base change and tensor construction.
- msearch leansearch: "Kahler differentials commute with simultaneous outer
  scalar extension and explicit ring and module tensor reassociation".
  Eight hits, again ordinary differential base change and induced maps.
- rg in Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: `OuterBaseChange|outerBaseChange|outer_base_change`
  has no matches. A second project search for the full node id has no matches.
- rg of `cancelBaseChange|tensorKaehlerEquiv|baseChange.*ifferential` in the two
  project Lean roots found tensor reassociations in other statements and the
  ordinary base-change theorem in `IsEtaleAtFieldExtensionDescent`, not this item.
  Read Mathlib `Kaehler/TensorProduct.lean` in full through the comparison
  definitions, and `TensorProduct/Maps.lean` at its tensor cancellation.
  Also read the upstream `Mathlib/RingTheory/IsTensorProduct.lean` interface:
  it changes the opposite tensor factor and does not state this whole theorem.

Validation: prescribed scompile.py compiled the module in sandbox mode and by
its library module name, cleanly (3.4 s and 1.9 s); all declarations have explicit
universe and variable binders. Only `comparison` contains `sorry`. There are no
hollow definitions and no disputed statement or node fault.

## Second reading by Q43

A separate serial reading in this worker session reopened the node and final
Lean text and checked all seven conjuncts and all four ring hypotheses against
the node. No separate agent was started, as the dispatcher brief prohibits it;
the maintainer supplies the independent review. The first draft attempted to
reuse Mathlib's `moduleBaseChange' A T C`, which acts on Ω(C/A), not Ω(C/B).
That attempt was removed completely. The final version instead concludes the
module action together with its full defining formula, and explicitly supplies
that same action to h and F. This preserves relative differentials over B.
Both inverse formulas, the B_T-algebra condition on q, the C_T-linearity of h
and F, and the generator normalization are present. The ring map is the
specified tensor extension, not a fresh hypothesis. The source imposes neither
flatness nor finiteness, and the final signature imposes neither.

The first delivery preflight did not recognize named `scoped instance` declarations
in its declaration inventory. They were rewritten as ordinary public abbreviations
with `attribute [scoped instance]`, preserving exactly the same constructions and
scope, so the canonical helpers are now visible to that inventory.
