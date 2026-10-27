## Worker report

The module `Sheaf.AlgebraicGeometry.ComponentCartierBlowup` states
`AlgebraicGeometry.Scheme.exists_component_cartier_blowups`. Its sole proof is `sorry`.
No definition is introduced, no node statement is corrected, and no dependency record changes.
All variables and the universe `u` are explicitly bound (`autoImplicit false`).

Sources read: the complete item and its nine proof steps; all fourteen statement-dependency
statements and their recorded declarations/docstrings; ILO, Travaux de Gabber, Expose X 2.3,
Step 1, printed p.150 (PDF p.156); Stacks `divisors.tex`,
`lemma-blow-up-integral-scheme` (02ND) and
`lemma-blowing-up-gives-effective-Cartier-divisor` (02OS), including their proofs.
ILO takes reduced irreducible components and blows up the marking; 02ND gives integrality
and 02OS gives the complement isomorphism and effective Cartier exceptional divisor.

Hypotheses and clauses, in statement order:

- Field e: `(e : Type u) [Field e]`.
- An e-scheme T: `(T : Scheme.{u}) (p : T ⟶ Spec (.of e))`; this is its structure map.
- Nonempty, reduced, proper and finite type: `[Nonempty T] [IsReduced T] [IsProper p]`.
  Mathlib's `IsProper` extends `LocallyOfFiniteType`; its `UniversallyClosed` parent gives
  `QuasiCompact`. Thus the finite-type hypothesis is present through these existing
  instances, with no extra restriction and no separate overlapping instance binders.
- C closed and nowhere dense: `(C : Closeds T)` and
  `hC : interior (C : Set T) = ∅`. As C is closed, this is exactly nowhere density.
- A finite nonempty enumeration: `∃ (s : ℕ) (_ : 0 < s)` and the equivalence
  `Fin s ≃ {Z : Set T // Z ∈ irreducibleComponents T}`. An equivalence ensures that
  every component occurs, exactly once.
- Reduced induced component structures: `Ti`, inclusions `ι`, `IsClosedImmersion (ι i)`,
  `Set.range (ι i) = (components i).val`, and `hTi : IsIntegral (Ti i)`. Integrality
  supplies reducedness and nonemptiness; a reduced closed immersion with that image is
  precisely the reduced induced subscheme (uniqueness in the existing reduced-induced
  closed-subscheme theorem). The existential component schemes are therefore pinned
  to the stated objects up to their unique isomorphisms over T.
- Each component is integral and proper: `hTi` and `IsProper (ι i ≫ p)`.
- Reduced marking and its ideal: the closed set `C.preimage (ι i).continuous` is C∩Ti
  on Ti, and the equality `I i = IdealSheafData.vanishingIdeal (...)` pins the ideal
  to its reduced induced structure. Its scheme is `(I i).subscheme` with canonical
  closed immersion `(I i).subschemeι` and kernel `I i`. This uses the existing
  constructions, rather than replacing the marking by a possibly nonreduced pullback
  subscheme or by an arbitrary ideal with the same support.
- Quasi-coherent finite-type ideal: `I i : (Ti i).IdealSheafData` is exactly the
  project's quasi-coherent ideal-sheaf interface; `∀ V, ((I i).ideal V).FG` is the
  finite-type condition used by the recorded blowup properness theorem.
- Complement: `U i = (C.preimage (ι i).continuous).compl` fixes the open subscheme;
  `Nonempty (U i)`, `IsCompact (U i : Set (Ti i))`, and `Dense (...)` state all
  three claimed properties, including quasi-compactness.
- Ordinary blowup and its map: `(I i).blowup` and `(I i).blowupMap` are the recorded
  glued ordinary blowup; there is no replacement by an unspecified modification.
- Proper and surjective blowup map: `IsProper (I i).blowupMap` and
  `Surjective (I i).blowupMap`.
- Nonempty integral proper finite-type source: `hS : IsIntegral (I i).blowup`
  (includes nonemptiness), plus `IsProper`, `LocallyOfFiniteType`, and `QuasiCompact`
  of `(I i).blowupMap ≫ ι i ≫ p`.
- Complement isomorphism and dense inverse image:
  `IsIso ((I i).blowupMap ∣_ U i)` and
  `Dense ((I i).blowupMap ⁻¹' (U i : Set (Ti i)))`. Together with density of U these
  say exactly that this blowup identifies dense open subschemes, the node's stated
  meaning of birationality; no separate competing birationality notion is introduced.
- Function fields: the existential `K` is an isomorphism between Mathlib's
  `Scheme.functionField` of Ti and its blowup. The bound integral proofs supply the
  irreducibility instances explicitly, so the clause does not assume integrality
  before proving it. The equality `hη` identifies the generic points under the
  blowup, and `K.hom = ...stalkCongr... ≫ ...stalkMap...` requires precisely the
  canonical induced identification. `stalkCongr` is oriented from the chosen generic
  point of Ti to the image of the chosen generic point of the blowup (`hη.symm`).
  This is stronger than an unconnected abstract field isomorphism only in how it
  spells out what the node means by the blowup identifying function fields.
- Cartier ideal and support: `((I i).comap (I i).blowupMap).IsInvertible` is literally
  the recorded effective-Cartier-ideal predicate, defined by local non-zero-divisor
  generators. Its support equality is to the inverse image of the actual C∩Ti.
- Empty-center case: `(C.preimage ... : Closeds (Ti i)) = ⊥ → I i = ⊤ ∧ IsIso ...`.
  Since the glued blowup and Ti have different Lean types, identity means the
  canonical isomorphism has hom equal to the blowup map (`asIso` of that map).
  Under this identification the map is the identity, just as in Stacks 02OS.

Dependency declarations used (full module and declaration):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`,
  `AlgebraicGeometry.IsIntegral`, `AlgebraicGeometry.irreducibleSpace_of_isIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.IdealSheafData`,
  `Scheme.IdealSheafData.vanishingIdeal`, `Scheme.Hom.ker` (the ideal of the canonical
  marking inclusion is the existing kernel, by `ker_subschemeι`).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.IdealSheafData.subscheme`,
  `Scheme.IdealSheafData.subschemeι`. Reducedness uses the integral condition on the
  components and the vanishing ideal on the centers, never a new reduction.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`,
  `Scheme.IdealSheafData.blowupMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded node's arbitrary
  integral-scheme clause reuses `Scheme.functionField`, declared in
  `Mathlib.AlgebraicGeometry.FunctionField`; its `functionFieldOfComponents` is for
  the general reducible case and is not a second field for these integral schemes.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `Scheme.IdealSheafData.comap`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`, whose definition is the required local
  regular-principal condition, not a different abstract invertibility predicate.

Every recorded proof-dependency module is imported privately when it is not already
provided by a public import. Mathlib leaves are supplied by the Noetherian, Proper,
Properties and topological imports. The complete nine-step proof is in the theorem
 docstring; no proof has been supplied in this stage.

Edge cases checked before writing:

- Empty T is excluded explicitly; the number of components cannot be zero.
- T = Spec e and C empty: s = 1, ideal is the unit ideal, the blowup is canonically
  the identity, the Cartier support is empty, and the function-field map is the identity.
- Empty C on every component, or empty C on just one component, is allowed; the
  conditional is per component and imposes no nonempty-center assumption.
- A closed set containing a whole component is excluded by nowhere density in this
  Noetherian setting (the complement of the other finitely many components contains
  a nonempty open). This ensures the ideal is nonzero on each component.
- Intersecting reduced components are allowed: for a proper nodal curve and C a
  finite set of nodes, each component is its reduced induced structure and the
  marking on it is reduced. No disjointness of component images is assumed.
- Zero-dimensional components give an empty marking and the identity case.
- The unit ideal is a Cartier ideal (generator 1 is a non-zero-divisor), consistent
  with empty support. The forbidden zero ideal cannot occur on a nonempty component
  because it would make U empty.
- No assumption of perfectness, algebraic closure, positive characteristic, smoothness,
  geometric integrality or an equidimensional scheme is added.

Searches (all through the prescribed tools or read-only source searches):

- `msearch.py ... leanfinder "Blow up the reduced marking on each irreducible component
  of a proper reduced scheme to obtain integral proper birational models with effective
  Cartier boundary"`: eight hits about normalization and rational maps; no matching theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsIntegral, AlgebraicGeometry.IsProper"`:
  one hit, `AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`,
  about proper group objects; no match.
- `msearch.py ... leansearch "Blowing up an integral scheme in a nonzero ideal gives an
  integral scheme and an effective Cartier exceptional divisor"`: eight hits about
  `IsIntegral`, its constructor, and its basic permanence results; no match.
- `msearch.py ... grep "blowup|blow.up|ReesAlgebra|Cartier" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, `component_cartier`, `componentCartier`, component/blowup combinations,
  and `exists_component_cartier_blowups`: no duplicate declaration. Related declarations
  include reduced-blowup generic geometry and normalized blowups, but neither states
  this component enumeration, canonical reduced marking and Cartier conclusion.
- Direct reads of the recorded blowup, complement, principalization, finite-type ideal,
  reduced-induced closed-subscheme, function-field, and Cartier declarations confirmed
  that every needed notion already exists. No new definition node is needed.

No STATEMENT-DISPUTED flag and no node fault were found. The historical example
`Sheaf.CategoryTheory.CompactObject` is now withdrawn; its node points to the upstream
copy. This delivery follows the current module-mode convention and the live example
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` instead.

## Second reading by Q20

A second pass by the same dispatcher worker, without claiming an independent agent
review (the assignment forbids spawning agents); the maintainer's independent review
follows delivery. I reopened the item and the completed module together. I checked
all hypotheses and all clauses against the correspondence above, with special attention
to the finite enumeration being an equivalence, not a mere list covering some components;
the reduced center being the vanishing ideal, not the nonreduced scheme-theoretic inverse
image; and the field isomorphism being tied to the actual stalk map. I checked that
`hη.symm` gives the correct source for that map and that all integral and nonempty
conclusions are inside the existential, not hypotheses. The explicit generic-point
applications initially omitted the QuasiSober argument; the compiler exposed this and
it was repaired. The next compile reported overlapping proper/finite-type binders and
one overlong line; the redundant instance binders were removed (finite type is already
implied by properness) and the line wrapped. The empty-center clause uses the canonical
isomorphism interpretation of identity, preserving the source's assertion for the actual
glued blowup. No mathematical statement change or additional hypothesis was necessary.

Validation: the final source compiled cleanly through the prescribed `scompile.py`
on the server, both as the sandbox module (2.2 seconds) and under its library module
name (3.2 seconds), with no warnings or errors.
