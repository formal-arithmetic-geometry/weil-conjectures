## Worker report

The module `Sheaf.CategoryTheory.NaturalComparisonStrictIntertwiners` states
`CategoryTheory.Endofunctor.Algebra.naturalComparisonStrictIntertwiners`, with one
postponed theorem proof and no new definitions. The source is the entire proof of
`prop-pur-weil-equivariance-scheme-frobenius` in the main-20261015 blueprint,
especially its final sentence about precomposing vertical arrows. The theorem
docstring gives all four proof steps from the reviewed node.

Hypotheses and clauses, matched individually:

- The category is `{C : Type u} [Category.{v} C]`, with independent, explicitly
  bound object and morphism universes. The two endofunctors are `(F G : C ⥤ C)`.
- The natural isomorphism is `(kappa : F ≅ G)`. Its naturality and inverse
  identities are supplied by Mathlib's definition; no extra square hypothesis
  is assumed.
- The two objects are `(M N : C)`; their structure maps are
  `(phiM : G.obj M ⟶ M)` and `(phiN : G.obj N ⟶ N)`. These maps are arbitrary.
- The common lower arrow is `(h : M ⟶ N)`. In diagrammatic composition order,
  the first conjunct is exactly `phiM ≫ h = G.map h ≫ phiN` if and only if
  `(kappa.hom.app M ≫ phiM) ≫ h = F.map h ≫ (kappa.hom.app N ≫ phiN)`.
  Thus the lower arrow is literally the same `h`, and the upper arrows are
  respectively `G.map h` and `F.map h`.
- The definitions of u_M and u_N are written as the actual composite terms
  `kappa.hom.app M ≫ phiM` and `kappa.hom.app N ≫ phiN`. No opaque parameter,
  local notation, or statement-level let replaces these composites.
- The second conjunct is conditional on `IsIso phiM`. It asserts `IsIso` of
  u_M, identifies its `inv` with `inv phiM ≫ kappa.inv.app M`, and states both
  composites with this inverse: the identity of `F.obj M` and the identity of
  `M`, in that order. The third conjunct repeats all four clauses for N,
  conditional independently on `IsIso phiN`. No invertibility is assumed for
  the initial intertwiner equivalence.
- The final conjunct gives a functor T from the full subcategory of G-algebras
  with invertible structure maps to the corresponding full subcategory of
  F-algebras. Its equality after the full-subcategory inclusions says it is
  precisely Mathlib's `functorOfNatTrans kappa.hom` restricted to these objects.
  Reading that definition shows its carrier is unchanged, its structure is
  `kappa.hom.app A.a ≫ A.str`, and the underlying arrow of its map is `h.f`.
  This equality specifies the transport, rather than asserting existence of an
  arbitrary functor or only a forgetful comparison up to isomorphism.

Dependency declarations read and used:

- `def-nagata-category` is a Mathlib leaf: `CategoryTheory.Category` in
  `Mathlib.CategoryTheory.Category.Basic`, including `CategoryStruct` and the
  identity and associativity laws. It is publicly available through the algebra
  import.
- `def-weil-endofunctor-fixed-pair-category` is a Mathlib leaf with an explicit
  specialization: `CategoryTheory.Endofunctor.Algebra` and its `Hom`, `forget`,
  and `functorOfNatTrans` in `Mathlib.CategoryTheory.Endofunctor.Algebra`, together
  with `CategoryTheory.ObjectProperty.FullSubcategory` and `ObjectProperty.ι`
  from `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`. The theorem uses
  exactly the specified full subcategory on `IsIso A.str`. These same two nodes
  are all the proof dependencies, so no additional proof import is required.

Edge cases checked before drafting: no object or arrow is required to be
nonzero or invertible in the first conjunct. Zero/noninvertible structure maps
are allowed there. Either conditional inverse clause may apply independently
of the other. Identity kappa reduces to the original equation and inverse;
identity h gives the usual structure-map comparison. Terminal categories cause
no obstruction. For an empty category the theorem's object binders have no
instances, and the strict-category transport itself is the unique empty
functor. No finite, additive, abelian, or small-category assumption is imposed.
The inverse equations have the correct types F(M) → F(M) and M → M,
respectively (and likewise for N).

Searches for an exact existing statement:

- `msearch.py` LeanFinder: "A natural isomorphism between endofunctors preserves
  and reflects intertwining arrows and transports invertible structure maps".
  Eight hits, including `Functor.mapActionCongr`, `NatIso.isIso_map_iff`, and
  conjugation results, give related constructions but not this statement.
- `msearch.py` Loogle: `CategoryTheory.Endofunctor.Algebra.functorOfNatTrans`.
  Twelve hits, including `functorOfNatTrans`, its object/arrow formula lemmas,
  and `equivOfNatIso`. Read the complete definitions and docstrings: they
  transport unrestricted algebras but do not state the bidirectional equation,
  the conditional explicit inverses, and the strict restriction together.
- `msearch.py` Mathlib grep: `functorOfNatTrans|equivOfNatIso|isIso_comp`
  in CategoryTheory. Twenty-five hits: the algebra transport and general
  composition invertibility ingredients, with no exact complete statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `FixedPair|fixedPair|strictIntertwin|naturalComparison`, then
  `naturalComparisonStrictIntertwiners|strict.intertwin|intertwiner` in the
  relevant category theory files: no exact match. The sibling
  `NaturalComparisonFunctorTransport` concerns transport along an additional
  functor L and comparison squares in two categories, so it is distinct.
  A recursive search for this node id in `lean/WeilConjectures` found no result.
- Read both statement-dependency nodes' complete statements, Mathlib matches,
  and the corresponding source declarations. Neither requires an interface
  repair or a new definition node.

The node's statement and other non-Lean fields remain unchanged. The existing
Q126 review is a stage-1 split review, and the base has no `lean` record or
`reviewed_lean` record. There is no repair note for this item. No mathematical
statement fault or STATEMENT-DISPUTED issue was found. The prescribed
single-file compiler is used for validation; its initial field-notation errors
were repaired by naming `ObjectProperty.FullSubcategory` and `ObjectProperty.ι`
explicitly, without adding a definition.

The worker delivers directly under the current dispatcher brief; the
maintainer supplies the independent review.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
