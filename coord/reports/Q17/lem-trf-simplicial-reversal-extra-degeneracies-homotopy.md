## Worker report

The delivery states the node without changing its natural-language statement or
any dependencies. Its module is
`Sheaf.AlgebraicTopology.SimplicialReversalTransport`. It has one concrete helper
`CategoryTheory.SimplicialObject.Augmented.ordinalReverse` and eight named theorems,
all with `sorry` proofs. The existing reversal declarations and the eight new
statements together realize the node; all are listed in `lean.declarations`.
The new definition constructs its actual data by precomposition, without any
choice or postponed data. There are no new nodes or dependency repairs.

Source read: `literature/stacks-project/simplicial.tex`,
`lemma-standard-simplicial-homotopy` (Tag 08ND), especially its second homotopy
equivalence, and the nine explicit auxiliary index-calculation steps of this node.
The Stacks lemma is the application; the DAG correctly attributes the additional
reversal calculation to an agent. There was no item-specific repair note.

The recorded dependency interfaces were read in full:

- `def-weil-pbc-simplicial-object`: the Mathlib module
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject`, `.δ`, `.σ`, and their docstrings. It is the
  functor category on `SimplexCategoryᵒᵖ`, and its arrows are natural transformations.
- `lem-coef-simplicial-extra-degeneracy-prism`: its `mathlib_match` is
  `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopy` in
  `Mathlib.AlgebraicTopology.ExtraDegeneracy`. Read its `ExtraDegeneracy` structure,
  `map`, `section_`, `section_comp_hom`, and `homotopy`, together with the complete
  `CategoryTheory.SimplicialObject.Homotopy` structure and `whiskerRight` in
  `Mathlib.AlgebraicTopology.SimplicialObject.Homotopy`. These give exactly the
  stated left extra-degeneracy and prism endpoint conventions; no repair is needed.

Both dependency modules are public transitive imports of the two public imports
of the delivered module. There are no proof-only dependencies beyond these.

Clause-by-clause correspondence (composition in Lean is written in diagram order):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| An arbitrary ordinary category C | `{C : Type u} [Category.{v} C]`; object and morphism universes are independent, with `autoImplicit false`. |
| Order-preserving alpha and r(alpha)(j) = n-alpha(m-j) | Imported `SimplexCategory.rev` and `SimplexCategory.rev_map_apply`: `Fin.rev` is precisely subtraction from the last index. Its data use `Hom.mk` of the reversed monotone map. |
| r is a functor and involution | The actual imported functor `SimplexCategory.rev`, its functor laws, `rev_map_rev_map` and `revCompRevIso`. No private reversal is introduced. |
| W^r = W precomposed by r.op, and W^r_n = W_n | Imported root namespace `SimplicialObject.opFunctor` is exactly this precomposition; `opObjIso` is `Iso.refl`. |
| Reversed faces d_i = d_(n-i) | Imported `SimplicialObject.opFunctor_obj_δ`, using `i.rev` with `i : Fin (n+2)` for faces out of degree n+1. |
| Reversed degeneracies s_i = s_(n-i) | Imported `SimplicialObject.opFunctor_obj_σ`, using `i.rev` with `i : Fin (n+1)` on degree n. |
| r(q_n) = q_n and the unchanged explicit section operator | `ordinalReverse_terminal`: the first conjunct fixes `isTerminalZero.from`; the next two are equality of the operators and their composites with the supplied t. |
| Augmentation p:W -> const Y | `X : Augmented C`: `X.left = W`, `X.right = Y`, `X.hom = p`, using Mathlib's existing comma category. |
| p^r and unchanged p_n | `X.ordinalReverse` has left `opFunctor.obj X.left`, right `X.right`, hom `Functor.whiskerLeft SimplexCategory.rev.op X.hom`. Its degree components are definitionally `X.hom.app n`. Imported `opFunctor_map_app` gives the general arrow statement. |
| Supplied t_-1 and t_n | The binders `t' : X.right ⟶ X.left _⦋0⦌` and `t : ∀ n, X.left _⦋n⦌ ⟶ X.left _⦋n+1⦌` of `exists_extraDegeneracy_ordinalReverse`. |
| p_0 t_-1 = identity | `hε : t' ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right`. |
| d_(n+1) t_n = identity | `hlast : ∀ n, t n ≫ X.left.δ (Fin.last (n+1)) = 𝟙 (X.left _⦋n⦌)`. |
| d_0 t_0 = t_-1 p_0 | `hfirst : t 0 ≫ X.left.δ 0 = X.hom.app (op ⦋0⦌) ≫ t'`. |
| d_i t_(n+1) = t_n d_i, 0≤i≤n+1 | `hδ` quantifies `i : Fin (n+2)`; `i.castSucc` denotes the same index in the faces out of degree n+2, excluding only its last face. |
| s_i t_n = t_(n+1) s_i, 0≤i≤n | `hσ` quantifies `i : Fin (n+1)`; `i.castSucc` denotes the same index among degeneracies out of degree n+1. |
| Exactly the same maps give left extra-degeneracy data | Conclusion `∃ ed : Augmented.ExtraDegeneracy X.ordinalReverse, ed.s' = t' ∧ (∀ n, ed.s n = t n) ∧ ...`. The actual Mathlib structure imposes exactly the five left-data equations of the dependency; no extra relation is assumed. |
| The explicit section is unchanged | The third conjunct states `ed.section_.app (op ⦋n⦌) = t' ≫ X.left.map q_n.op`. |
| Any simplicial section a^r becomes a section a with the same components | `exists_section_of_ordinalReverse` accepts arbitrary `b` with `hb : b ≫ X.ordinalReverse.hom = 𝟙 _`, and supplies `a` with `a ≫ X.hom = 𝟙 _` and every `a.app n = b.app n`. |
| Arbitrary A,B,f,g and H from f^r to g^r | `exists_homotopy_of_ordinalReverse` takes arbitrary `f g : A ⟶ B` and `H : Homotopy (opFunctor.map f) (opFunctor.map g)`. |
| Htilde_j^n = H_(n-j)^n is a homotopy from g to f | Its conclusion gives `K : Homotopy g f` and `∀ n (i : Fin (n+1)), K.h i = H.h i.rev`. This supplies all seven families of identities, not merely endpoints or the existence of an unrelated homotopy. |
| Natural maps of supplied extra-degeneracy diagrams | `ordinalReverse_extraDegeneracy_naturality` uses an actual augmented arrow `u`, degree-zero compatibility `hzero`, and all higher compatibilities `hdeg`; its conclusion is precisely those equations after reversal and the commuting square for the explicit sections. |
| Naturality for arbitrary transported sections | `ordinalReverse_section_naturality` takes any original and transported sections with equal components and a compatible square `hb` on reversed diagrams; its conclusion is the square of natural transformations on the original diagrams. The fact that they are sections is unnecessary for this compatibility calculation. |
| Natural maps of supplied homotopy diagrams | `ordinalReverse_homotopy_naturality` takes `u`, `v`, compatible H,H', and any K,K' with the specified reversal formulas. Its conclusion is the corresponding compatibility of K,K'. This does not impose a pointwise choice. |
| Evaluation in any parameter functor category | `ordinalReverse_whiskering` gives exact compatibility of reversal with arbitrary postcomposition F on objects, arrows and augmentations. The functor clauses in the three existence theorems specify the evaluated extra-degeneracy maps, explicit sections, arbitrary section components and homotopy components. Specialize C to a functor category and F to its evaluation functor at any parameter. The results apply directly in that category before evaluation. |

The component equalities make the existential outputs completely determined:
extra degeneracy data are the supplied t',t; sections are determined by their
natural-transformation components; homotopies are determined by their h maps,
since all remaining fields are proofs. No object is defined by choosing from a
mere existence claim. The helper augmentation has explicit data. No additional
limits, zero objects, additive structure, model structures or size equalities
are assumed.

Edge cases checked before finalizing:

- At degree zero there is exactly one homotopy index, `0 : Fin 1`, which reversal
  fixes; the two faces are exchanged, so the endpoint order is g to f.
- `hlast` at n=0 is d_1 t_0 = identity, while `hfirst` is d_0 t_0 = t_-1 p_0;
  these give the two distinct required equations, with no off-by-one collision.
- The face compatibility indices have range 0..n+1 and the degeneracy indices
  have range 0..n. Their target-degree inclusions exclude just the final
  operator, as the right-extra-degeneracy formulas require. Reversal maps these
  to indices 1..n+2 and 1..n+1, respectively, exactly Mathlib's left data.
- For n=0, q_0 is the identity and the explicit section is t_-1.
- Empty categories give no augmented objects, without a hidden inhabitance
  assumption. Nonempty categories, including those without zero objects or
  limits, are unrestricted. For an empty parameter category the results still
  hold in the functor category; evaluation is quantified only where a parameter
  is actually given.
- C,D have independent object and morphism universes; postcomposition/evaluation
  does not force site or parameter universes to coincide.

Searches actually run through msearch.py, as recorded in the sandbox search log:

- LeanFinder, `Ordinal reversal transports right extra degeneracies to left extra
  degeneracies and reverses endpoints of a combinatorial simplicial homotopy`:
  eight hits. The useful ones are `SimplexCategory.rev_map_apply`, `.rev_map_δ`,
  `.rev_map_σ` and simplicial-set operator formulas; none gives the full transport.
  All useful existing general-category reversal declarations were reused.
- Loogle, `SimplicialObject.Homotopy, SimplicialObject.opFunctor`: parser reported
  unknown identifier `SimplicialObject.Homotopy`; this is not a no-match result.
  Repeated with the supported string query `"Homotopy", "rev"`: four hits,
  all chain-complex prevD identities or localization, not this simplicial result.
- LeanSearch, `A combinatorial homotopy on ordinal reversed simplicial objects
  transports to a homotopy with opposite endpoints`: eight hits, including
  `SimplicialObject.opEquivalence` and `SimplexCategory.rev_map_apply`, together
  with short-complex, cochain-complex and path homotopies. These do not give the
  requested right-to-left data or combinatorial homotopy transport.
- Mathlib grep, `rev|reverse|opFunctor` under
  `AlgebraicTopology/SimplicialObject`: found `Op.lean`. Read that whole file,
  `SimplexCategory/Rev.lean`, the complete Homotopy structure, and the relevant
  ExtraDegeneracy source. There is no reversal of combinatorial homotopies.
- Local rg over `lean/WeilConjectures` and `lean/Sheaf`, by item id and the
  reversal/extra-degeneracy/homotopy names: no implementation of this transport.
  The already landed `AdjunctionStandardSimplicialHomotopy.lean` mentions this
  argument in its proof docstring, but does not state the auxiliary transport.
  The upstream declaration-name index was also searched. No duplicate notion
  was created; no new definition node was needed.

Validation: scompile.py compiled the sandbox and final module paths separately,
with the full public module header and `autoImplicit false`, cleanly with no
unexpected warnings. The initial namespace resolution issue was repaired by
opening the root `SimplicialObject` namespace that owns Mathlib's `opFunctor`;
all delivered declarations use the actual Mathlib objects. All eight postponed
theorems have source/blueprint docstrings containing the relevant steps of the
node's natural-language proof. No statement fault or dispute was found.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
