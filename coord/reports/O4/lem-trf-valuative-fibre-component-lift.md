## Worker report

The module `Sheaf.AlgebraicGeometry.ValuativeFibreComponentLift` states
`AlgebraicGeometry.exists_valuative_fibre_component_lift`, with its sole proof `sorry`.
It matches Stacks Project Tag 0GSH (`more-morphisms.tex`,
`lemma-make-base-change`, lines 5093–5160), which I read in full, including the proof.
The node is unchanged except for its `lean` record. There are no new definitions,
new nodes, dependency repairs, statement corrections, or disputed statements.

Hypotheses and all clauses, matched to Lean:

- An arbitrary scheme morphism `f : X ⟶ S` is bound with `X S : Scheme.{u}`.
  There are no finiteness, flatness, separatedness, or Noetherian hypotheses.
- The specified point is `(y : X)`; the notation `t = f(y)` is eliminated by
  writing `f y` wherever the statement uses `t`.
- The reduced integral closed subscheme `Y = closure {y}` is presented by
  `(i : Y ⟶ X) [IsIntegral Y] [IsClosedImmersion i]` and
  `hY : Set.range i = closure ({y} : Set X)`.
  These conditions express exactly the stated subscheme structure: integral implies
  reduced, and a reduced closed immersion with this image is uniquely the reduced
  induced closed subscheme, up to its unique isomorphism over `X` (Stacks 01J3/01J4).
  This is a presentation of the specified object, not an extra geometric restriction
  or a replacement by an arbitrary scheme with the same underlying space.
- The special base point is `(s : S)`. The given `x` is bound directly as a point
  of the actual scheme-theoretic fibre `(i ≫ f).fiber s`.
  Its ambient image, denoted `x` in the source, is `i ((i ≫ f).fiberι s x)`.
  `(C : Set ((i ≫ f).fiber s))`, `hC : C ∈ irreducibleComponents ...`, and
  `hx : IsGenericPoint x C` say that it is a generic point of a component.
- The valuation ring is the existential `A : Type u` with `CommRing A`,
  `IsDomain A`, and `ValuationRing A`. Mathlib uses total divisibility of pairs
  of ring elements, which is equivalent to the source's fraction-field condition:
  apply total divisibility to a numerator and a nonzero denominator, and conversely
  apply the fraction-field condition to the quotient of two nonzero elements.
- The base change uses `g : Spec (CommRingCat.of A) ⟶ S` and exactly the chosen
  scheme fibre product `pullback f g`, with `pullback.fst f g` as `g'` and
  `pullback.snd f g` as `f'`. Thus its Cartesian property is built into the object.
- The points `t' s' : Spec (CommRingCat.of A)` satisfy
  `IsGenericPoint t' Set.univ` and `IsClosed ({s'} : Set (Spec ...))`.
  A valuation domain has an irreducible local spectrum, so these specify precisely
  its unique generic and closed points. They are allowed to coincide.
- Clause (2) is `g t' = f y ∧ g s' = s`.
- Clause (3) uses a point `z : (pullback.snd (i ≫ f) g).fiber t'`, a component `D`,
  `D ∈ irreducibleComponents ...`, and `IsGenericPoint z D`. This is the actual
  scheme `(Y ×_S Spec A)_{t'}` that the source explicitly identifies with
  `Y_t ×_{Spec κ(t)} Spec κ(t')`; the equality `g t' = f y` supplies the indicated
  base point. In particular, this is a scheme fibre after base change, not the
  topological inverse image of `Y_t` under `X' → X`, which could lose components.
- The ambient point `y' : (pullback f g : Scheme.{u})` satisfies
  `(pullback.snd f g) y' = t'` and `(pullback.fst f g) y' = y`.
  Its equality with the image of `z` under
  `pullback.map (i ≫ f) g f g i (𝟙 _) (𝟙 _) ...` after `fiberι t'`
  identifies it with the preceding generic component point. This is the canonical
  base-change closed immersion of `Y`, not a freely chosen map or lift.
  The two proof arguments to `pullback.map` are only categorical identity laws.
- Clause (4) binds `Y' : Scheme.{u}`, `IsIntegral Y'`,
  `i' : Y' ⟶ pullback f g`, and `IsClosedImmersion i'`, with
  `Set.range i' = closure ({y'} : Set (pullback f g : Scheme.{u}))`.
  As for `Y`, these are exactly a presentation of the reduced integral closure.
- The final point is bound in its actual scheme fibre:
  `x' : (i' ≫ pullback.snd f g).fiber s'`. A subset `E`, its membership in
  `irreducibleComponents`, and `IsGenericPoint x' E` give the special-fibre
  component condition. The last equality
  `(pullback.fst f g) (i' ((i' ≫ pullback.snd f g).fiberι s' x')) =
    i ((i ≫ f).fiberι s x)`
  is precisely `g'(x') = x` in ambient points.
- Residue fields are those in the recorded Mathlib `Scheme.Hom.fiber`, namely
  pullback along `Scheme.fromSpecResidueField`, using `Scheme.residueField`.
  No new residue field or field-extension interface is introduced.

Recorded dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (scheme locally affine locally ringed space; the morphism type).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`; its fields are nonemptiness and domain section
  rings on every nonempty open. The same file gives reducedness and irreducibility.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, whose full
  definition is `closure ({x} : Set α) = S`.
- `def-weil-irreducible-components`: its Mathlib match in
  `Mathlib.Topology.Irreducible`, `irreducibleComponents`, defined as
  `{s | Maximal IsIrreducible s}`. The node has status `mathlib`, so it needs no
  additional Lean record.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `Scheme.Hom.fiber`, `fiberι`, and `fiberToSpecResidueField`; I also read
  `fiberHomeo`, which identifies a fibre with the corresponding point inverse image.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
  I read the current published module through `scompile.py --source` because it
  is absent from the older source checkout. Its header and node record explicitly
  prescribe `Limits.pullback`, `pullback.fst`, and `pullback.snd` for scheme base
  change; `moduleBaseChange` concerns modules and is not the operation here.
  Its `baseChange_fiber` states the canonical fibre identification.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and
  `Scheme.fromSpecResidueField`; their signatures and docstrings were read.
- The proof dependency `def-pc-fibre-product` uses
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`, and `pullback.map`.
- The proof dependency `lem-trf-valuation-ring-specialization-lift` has no Lean
  record in the current node, but its source and `lean_candidates` identify the
  already proved `Scheme.exists_valuationSubring_of_specializes` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion`.
  I read its complete signature, docstring, and proof (lines 214–235), and import
  that module for the future proof. No duplicate theorem is required.
- The structural closed-immersion encoding is the existing Mathlib
  `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; its fields are a closed
  embedding and surjectivity on stalks. Valuation rings use the existing Mathlib
  class in `Mathlib.RingTheory.Valuation.ValuationRing`.

Edge cases checked before writing: an empty `X` supplies no `y`; an empty `Y_s`
supplies no `x`; neither case asks for a valuation ring. The zero ring is excluded
exactly by the domain requirement in the source. If `s = t` or `y` is closed,
a field is allowed as a valuation ring and `s' = t'` is allowed. No distinctness,
discrete valuation, rank, dimension, finite type, or characteristic condition is
imposed. Multiple components and non-Noetherian fibres remain permitted.
Nilpotents in `X` and `S` are allowed; only the specified reduced closures are
integral. All schemes and the valuation ring use universe `u`; this does not
restrict the existence assertion, since the source proof can take a valuation
subring of the algebraic closure of the residue field of `y`, which lies in `u`.
Every variable and universe is explicitly bound; no local notation, local
instance, private definition, or statement `let` is used.

Searches for an existing exact statement:

- `msearch.py`, leanfinder: “valuation ring base change lifts generic points of
  irreducible components in generic and closed fibres”. Eight results include
  `ValuativeCriterion.Existence.specializingMap`, `Flat.generalizingMap`,
  `ValuativeCommSq.field`, and fibre structure maps. None lifts both component
  generic points as in Tag 0GSH.
- `msearch.py`, loogle: `AlgebraicGeometry.Scheme, ValuationRing`. Two results,
  `ValuativeCommSq.valuationRing` and `ValuativeCommSq.mk`; neither is this theorem.
- `msearch.py`, grep in Mathlib `AlgebraicGeometry`:
  `valuation.*(component|generic)|component.*valuation`. No results.
- `msearch.py`, leansearch: “valuation ring base change generic points of
  components of closure fibres”. Eight results include `genericPoints.component`,
  `ValuativeCriterion.Existence.stableUnderBaseChange`, and valuation-ring classes;
  none is an exact statement.
- Source and project `rg` searches for the item id, the chosen declaration name,
  and valuation/component combinations found no exact theorem. Broad
  valuation/component text also finds unrelated evaluation components and a
  discrete-valuation relative-component lemma, neither an instance of this result.
  Searches of reduced-closure material found the existing integral closed-immersion
  presentation and reduced induced closed-subscheme uniqueness interface, so no
  duplicate notion or helper definition was introduced.

Validation: `scompile.py` compiled the statement both as a sandbox file and at its
library module path without errors or warnings after making the scheme coercion
explicit on `y'` and its ambient closure. The one theorem remains `sorry`, as
required in stage 2. The delivery dry run below checks the final import list,
exact signature record, and final file again.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
