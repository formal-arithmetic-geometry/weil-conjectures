## Worker report

This delivery states `lem-trf-adjunction-standard-simplicial-homotopy` in
`Sheaf.CategoryTheory.AdjunctionStandardSimplicialHomotopy` and supplies the definition node `def-trf-comonad-standard-resolution` in
`Sheaf.CategoryTheory.ComonadStandardResolution`. Only the item theorem is postponed
with `sorry`; the definition module contains no theorem and no `sorry`.
All helper definitions have explicit data; no object is selected from a postponed
existence assertion. No statement correction or disputed statement is needed.

The node-to-Lean correspondence, hypothesis by hypothesis and clause by clause:

- Ordinary categories S and A: `{S : Type uS} [Category.{vS} S]` and
  `{A : Type uA} [Category.{vA} A]`, with four independent universes. No limit,
  product, additivity, nonemptiness, faithfulness or smallness assumption is added.
- F left adjoint to U, unit, counit and both triangles: `{F : S ⥤ A}`,
  `{U : A ⥤ S}`, `(adj : F ⊣ U)`. These are Mathlib's actual adjunction data.
- G = FU and delta = F eta U: `adj.toComonad` has underlying functor `U ⋙ F`,
  counit `adj.counit`, and comultiplication
  `Functor.whiskerRight (Functor.whiskerLeft U adj.unit) F`.
  Lean's composition order is opposite to functional-order FU in the node.
- The terms X_n = G^(n+1), faces and degeneracies:
  `Comonad.IsStandardSimplicialResolution adj.toComonad B e`. Its first conjunct
  requires equality of the actual degree-n endofunctor and `resolutionPower G (n+1)`.
  Its face conjunct uses degree n+1 and i : Fin(n+2), with formula
  `whiskerRight (whiskerLeft (power G (n+1-i)) epsilon) (power G i)`.
  Its degeneracy conjunct uses degree n and i : Fin(n+1), with the corresponding
  `whiskerRight (whiskerLeft (power G (n-i)) delta) (power G i)`.
  Thus their functional-order formulas are exactly those in the node.
  `HEq` transports actual operators across equal source and target objects; it
  does not allow arbitrary isomorphic replacements or unconstrained maps.
- Simplicial identities: `B : SimplicialObject (A ⥤ A)` is an actual functor on
  the opposite simplex category, not just a family of face and degeneracy maps.
- Augmentation to a: `e : B ⟶ const.obj (𝟭 A)` with `HEq (e.app (op ⦋0⦌)) epsilon`.
  Evaluation at a yields X(a) → const(a). Naturality of the augmentation determines
  every component from degree zero.
- Naturality in a: B is endofunctor-valued and e is a natural transformation
  valued in that functor category. This also specifies the action on morphisms
  of A, because the term equalities are equalities of functors, not just objects.
- Applying U: `standardSimplicialRight B U` postcomposes each endofunctor by U.
  `standardSimplicialRightAugmentation B e U` is the actual whiskered e, composed
  with Mathlib's canonical constant-functor comparison.
- First homotopy equivalence: a simplicial section r, the strict section equation
  `r ≫ standardSimplicialRightAugmentation B e U = 𝟙 _`, and
  `Nonempty (SimplicialObject.Homotopy (augmentation ≫ r) (𝟙 _))`.
  The other inverse equation has the constant homotopy since it is strict.
- The section in degree zero is eta_Ua: `HEq (r.app (op ⦋0⦌))
  (Functor.whiskerLeft U adj.unit)`. In each degree it is this section followed
  by the operator of the unique [n] → [0], precisely the node's degeneracy extension.
- Second homotopy equivalence for every s: `standardSimplicialFree B F` precomposes
  every endofunctor by F; its augmentation is the actual precomposition of e.
  The section l satisfies `l ≫ augmentation = 𝟙 _` and has a homotopy from the
  identity to `augmentation ≫ l`. Evaluation at s gives the requested equivalence
  X(Fs) → const(Fs). The homotopy orientation follows the index reversal in the
  node's proof; homotopy equivalence does not require the opposite orientation.
- Homotopy has the meaning specified in the node: Mathlib's
  `SimplicialObject.Homotopy` is exactly its degree-raising family with all face
  and degeneracy identities (the supplied prism dependency's recorded declaration).
  The Set/cylinder sentence explains this same standard notion and is not an
  extra hypothesis or a claim about products existing in an arbitrary category.
  We use the general combinatorial notion, which in sets has the stated cylinder
  interpretation. We do not substitute the preadditive chain-complex homotopy API.

Dependency declarations read and used:

- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject`, `.δ`, `.σ`, `.const`; these are exactly
  `def-weil-pbc-simplicial-object`'s recorded declarations. Also `.Augmented`
  and the postcomposition APIs were read when choosing the interface.
- `Mathlib.AlgebraicTopology.ExtraDegeneracy`:
  `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`, `.section_`,
  `.section_comp_hom`, `.homotopy`; these are the general-category prism node's
  Mathlib match and its Set specialization's match. The module is imported as a
  proof dependency. Its full data, section and homotopy signatures were read.
- `Mathlib.AlgebraicTopology.SimplicialObject.Homotopy`:
  `CategoryTheory.SimplicialObject.Homotopy` and its complete identities.
- `Mathlib.CategoryTheory.Monad.Basic`: `CategoryTheory.Comonad`, with exactly
  coassociativity and the left and right counit equations.
- `Mathlib.CategoryTheory.Monad.Adjunction`: `CategoryTheory.Adjunction.toComonad`;
  read its entire definition, counit, comultiplication and triangle-law proofs.
- `Mathlib.CategoryTheory.Whiskering` and `Functor.Const` (through the above imports):
  actual `whiskeringLeft`, `whiskeringRight`, `whiskerLeft`, `whiskerRight`,
  `Functor.constComp` for the canonical images of augmentations.
- This delivery's `CategoryTheory.Comonad.IsStandardSimplicialResolution` and
  `resolutionPower`, owned by `def-trf-comonad-standard-resolution`. The item cites
  that definition node in stmt_deps. The comonad existence theorem remains solely
  in proof_deps and is not delivered or imported, since it has no published module.

Edge cases checked before writing:

- Empty categories: no object or inhabitance is demanded; all conclusions remain
  functorial and cover the empty case without a nonempty binder.
- Identity adjunction: powers are identity functors; all operators, sections and
  homotopies have the constant resolution interpretation.
- Degree zero: degree-zero counit is prescribed; the first section is eta_Ua and
  its composite with U epsilon is the right triangle. The unique [0] → [0] is
  the identity, so the all-degree section condition is consistent at zero.
- Degree one: faces have indices 0 and 1 with formulas epsilon_G and G epsilon;
  sigma_0 in degree zero is delta. Both face-degeneracy identities are counit laws.
- Extremal indices: i=0 applies the counit/comultiplication at the outermost G,
  and i=n (respectively n+1 for degree n+1 faces) applies it at the innermost G.
  Fin bounds make the natural subtractions the required exponents.
- Free/forgetful adjunction: the terms are iterated free objects, the first
  section is a unit in the underlying category, and the free-object contraction
  uses F eta. No false contraction inside A for arbitrary nonfree a is asserted.
- Four independent universes prevent accidental restriction to small categories
  or equality of the object and morphism universes of either category.

Searches for an existing declaration (same searches also cover the prerequisite):

- msearch.py leanfinder, query `The standard augmented simplicial object of an
  adjunction is contractible after applying the right adjoint and on free objects`:
  8 hits, including Cech nerves and ExtraDegeneracy.homotopyEquiv; no match.
  Cech nerves add pullback assumptions, and homotopyEquiv is for alternating-face
  complexes in a preadditive category, so neither states this node.
- msearch.py loogle, query `"Comonad"`: 12 hits defining comonads, identities and
  forgetful constructions, no general simplicial resolution.
- msearch.py leansearch, query `A comonad defines a standard augmented simplicial
  object with iterated functors as terms`: 8 hits, including Comonad.mk and
  SimplicialObject.Augmented, none constructing the resolution.
- msearch.py grep, query `comonad.*[Ss]implicial|[Ss]implicial.*[Cc]omonad|barConstruction`:
  zero Mathlib hits.
- Direct rg on WeilConjectures and lean/Sheaf for standard simplicial, comonad
  simplicial, adjunction simplicial and the proposed names: no existing declaration.
  The module-cup Godement cosimplicial files concern a specialized monad/coefficient
  construction, not an ordinary-category comonad resolution.
- Direct rg for the exact item id on upstream WeilConjectures: zero hits.
- Read the complete existing DAG theorem prerequisite and its earlier searches.
  That node asserts existence, while the new definition node specifies the predicate
  on supplied resolution data. It neither asserts existence nor selects a witness.
- Read Stacks simplicial.tex, Example 0G5M/Lemma 0G5N and Situation 08N9/Lemmas
  08NC/08ND, including the complete proofs. In 08ND the self-composite written in
  its prose is in the wrong order; the node's proof and the Lean have the correctly
  typed section composite. This does not change the statement.

## New nodes

`def-trf-comonad-standard-resolution` owns the two plain definitions
`CategoryTheory.Comonad.resolutionPower` and
`CategoryTheory.Comonad.IsStandardSimplicialResolution` in its own module
`Sheaf.CategoryTheory.ComonadStandardResolution`. It defines the powers recursively
and the predicate specifying terms, whiskered counit faces, whiskered
comultiplication degeneracies, and the degree-zero counit augmentation. Its source
is Stacks Example 0G5M, with the augmentation specified in 0G5N. It asserts no
existence result. Its only DAG notion dependency is the existing simplicial-object
definition. The comonad is Mathlib's Comonad, with its three equations explicitly
spelled out in the node.

New search queries: LeanSearch `The prescribed powers faces degeneracies and
augmentation of the standard simplicial resolution of a comonad` returned eight
augmentation/extra-degeneracy/operator declarations; LeanFinder `Predicate
specifying the standard augmented simplicial object of a comonad using powers and
whiskered counit and comultiplication` returned eight general augmented-object
notions; Mathlib grep `resolutionPower|IsStandardSimplicialResolution|[Cc]omonad.*[Ss]implicial|[Ss]implicial.*[Cc]omonad`
returned zero hits. Direct rg with that pattern in upstream WeilConjectures and
lean/Sheaf also returned zero hits. DAG grep and blueprint_refs.py search found no
existing definition node for this predicate. The existing comonad-simplicial
node is a theorem asserting existence, and the other comonad definitions concern
specialized constructions. The actual search-tool JSON results are recorded
verbatim in the new node's mathlib_searches.

## Repair of the returned delivery

The maintainer upheld H2: the saved delivery attached the plain definitions to the
unlanded THEOREM node and added that theorem to stmt_deps, contrary to §1(A).
I extracted exactly those definitions into the new definition node above, changed
the item's import to its module, and replaced the added theorem stmt_dep by the
new definition id. I removed the theorem module and its node copy from this
packet. The theorem remains in the item's unchanged proof_deps. No theorem
statement, source formula, hypothesis, section or homotopy changed.

## Second reading by NB

I reopened the item, new definition node, their sources and both files and compared the
correspondence above. This is the dispatched worker's second pass; the maintainer's
independent review is still required and is not claimed here.

The first compile exposed that postcomposition of a constant simplicial functor
is not definitionally constant, because it maps an identity via U. I added
`Functor.constComp` to both actual augmentation helpers; it has identity components
and changes no map after evaluation. The prerequisite's equations, functor powers,
face indices, degeneracy indices and degree-zero counit were checked directly
against 0G5M/0G5N. The main theorem retains the adjunction, both contractions and
unit/degeneracy normalization; the homotopies live in the parameter functor
categories and so include naturality. No mismatch of mathematical statement was
found, and no hypothesis or conclusion was changed. All introduced helper data
are explicit and the item theorem has its source-based proof docstring. The new definition
module has no postponed proof.

Repair self-check: I compared the repaired item against current base: only lean
and the addition of the new definition id in stmt_deps differ. The comonad theorem
id occurs in proof_deps, never stmt_deps; neither its node record nor module is in
the packet. I read both definition signatures and all four predicate conjuncts:
the recursive powers start at identity, the degree-(n+1) face has Fin(n+2), the
degree-n degeneracy has Fin(n+1), and augmentation is the counit in degree zero.
The natural-language definition matches each conjunct and uses transport, not an
arbitrary isomorphism. The item signature is unchanged, so the earlier independent
maintainer reading of all its mathematical clauses still applies. This is a
self-check by the dispatched worker, not a claim of a newly independent reviewer.
