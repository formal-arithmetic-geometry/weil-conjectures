## Worker report

This delivery states `CategoryTheory.dualizable_iff_of_jointly_conservative` in
`Sheaf.CategoryTheory.DualizableJointlyConservativeLocality`, with one `sorry` and no
new definitions. The item node changes only in `lean`. There are no new nodes,
dependency repairs, statement corrections, disputed statements, or omitted proof imports.

Hypothesis and clause correspondence, checked against the full node:

- The category C is `{C : Type u} [Category.{v} C]`; the family is
  `{I : Type w} (D : I → Type u') [∀ i, Category.{v'} (D i)]`.
  Object, morphism and index universes are explicit and independent.
- The monoidal structures of `def-sfb-monoidal-category` are
  `[MonoidalCategory C]` and `[∀ i, MonoidalCategory (D i)]`.
  Their symmetry, naturality, involution, and hexagon are Mathlib's
  `SymmetricCategory` instances. The second hexagon stored by Mathlib follows
  from the first and symmetry, so this does not add a mathematical hypothesis.
- Chosen internal-Hom objects and natural adjunction bijections are the
  `MonoidalClosed` instances. Mathlib's `Closed.rightAdj` is chosen data,
  with `Closed.adj` the adjunction, not merely an existence assertion.
  Mathlib's convention is Hom(B ⊗ A,T) ≃ Hom(A,[B,T]). Therefore the node's
  transpose of g : A ⊗ B → T is rendered exactly as
  `curry ((β_ B A).hom ≫ g)`. In a symmetric category the correspondence between
  these choices is invertible: precompose with β in either direction. No
  particular internal Hom construction or normalization is imposed.
- The functors are `F : ∀ i, C ⥤ D i`. The strong structures of
  `def-sfb-strong-monoidal-functor` are `[∀ i, (F i).Monoidal]`. The dependency's
  Mathlib match explicitly identifies `CoreMonoidal` with this equivalent API:
  `CoreMonoidal.toMonoidal` converts the iso data; `Monoidal.εIso` and
  `Monoidal.μIso` recover the iso data from the forward/inverse maps.
- Compatibility of the tensorator with symmetry is exactly `hSymmetry`:
  `μ A B ≫ F.map (β_ A B).hom = (β_ (FA) (FB)).hom ≫ μ B A`.
- Joint conservativity is `hConservative`, quantified over every morphism a,
  with premise `∀ i, IsIso ((F i).map a)` and conclusion `IsIso a`.
- The internal-Hom isomorphisms are
  `h : ∀ i B, ihom B ⋙ F i ≅ F i ⋙ ihom ((F i).obj B)`.
  Their components are precisely F([B,T]) ≅ [FB,FT]. The natural-isomorphism
  structure gives naturality in T; `hHomNaturality` gives naturality in B
  using Mathlib's actual contravariant action `MonoidalClosed.pre`.
- Preservation of the stated transpose bijections is `hTranspose` for every
  i, A, B, T and g : A ⊗ B → T. Its left side is the target transpose of
  `μ A B ≫ F.map g`; its right side is F of the source transpose followed by
  `h i B` at T. Both transposes include the symmetry required by the preceding
  convention conversion. Composition is Lean's left-to-right `≫`.
- K is arbitrary `(K : C)`. Dualizability is
  `∃ E : C, Nonempty (ExactPairing K E)`: `ExactPairing K E` has evaluation
  E ⊗ K → 1, coevaluation 1 → K ⊗ E and both triangles. The conclusion is
  exactly the equivalence with the same property for every F i K in D i.
  `Nonempty` merely expresses existence of this real duality data; no data
  object is defined by an arbitrary choice or by `sorry`.
- Empty and infinite I are retained: there is no Nonempty, Fintype or Finite
  binder. No functor is individually assumed conservative, faithful or full.

Dependency declarations and full source interfaces read:

- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory`,
  `Mathlib.CategoryTheory.Monoidal.Category`, including `MonoidalCategoryStruct`
  data, tensor functoriality, naturality, pentagon and triangle.
- `def-sfb-strong-monoidal-functor`: `CategoryTheory.Functor.CoreMonoidal`,
  `Mathlib.CategoryTheory.Monoidal.Functor`, with its unit/tensor iso fields and
  all coherence laws; the same file's `Functor.Monoidal`, `εIso`, `μIso` API is
  used as authorized by the dependency's match.
- Proof dependency `lem-sfb-dual-tensor-adjunctions`:
  `CategoryTheory.tensorLeftAdjunction`, `tensorRightAdjunction` in
  `Mathlib.CategoryTheory.Monoidal.Rigid.Basic`; preservation declarations
  `Adjunction.leftAdjoint_preservesColimits` and `rightAdjoint_preservesLimits`
  in `Mathlib.CategoryTheory.Adjunction.Limits`. Rigid.Basic is public because
  the conclusion also uses its existing `ExactPairing` definition.
- Proof dependency `det-sp-unique-right-adjoint`:
  `CategoryTheory.Adjunction.rightAdjointUniq` and its transpose/counit
  compatibility in `Mathlib.CategoryTheory.Adjunction.Unique` (non-public import).
- Additional existing interfaces: `SymmetricCategory` in
  `Mathlib.CategoryTheory.Monoidal.Braided.Basic`; `Closed`, `MonoidalClosed`,
  `ihom`, `MonoidalClosed.curry`, `pre`, `internalHom`, and their naturality
  in `Mathlib.CategoryTheory.Monoidal.Closed.Basic` (exported by Rigid.Basic).

Source checked: the PDF of Hemo--Richarz--Scholbach, Lemma 4.5, first proof
paragraph, read with pdftotext: the lisse assertion follows because pullback is
monoidal, conservative, and commutes with inner Hom. The node expands this
formal implication to jointly conservative families. All eight supplied proof
steps are reproduced as the theorem's natural-language proof plan, including
normalization at the unit, compatibility on evaluation, joint conservativity,
and both triangle checks.

Edge cases checked before writing: the identity family says dualizability is
equivalent to itself; the terminal symmetric closed category satisfies every
condition; empty I makes joint conservativity assert every source morphism is
invertible, so it applies to the canonical comparison just as the proof says;
infinite I requires no finite selection or coproduct. A zero object in a
symmetric closed additive example has the usual zero dual pair. Non-dualizable
infinite-dimensional vector spaces cannot satisfy the reflection hypotheses
with all images dualizable, because the tensor/internal-Hom comparison would
be forced invertible. No additive, smallness, finiteness, or rigidity-of-all-
objects assumptions were introduced.

Searches performed on 2026-10-18:

- `msearch.py ... leanfinder`: "A jointly conservative family of strong
  symmetric monoidal functors preserving internal Hom reflects dualizable
  objects" returned eight results: reflective closed-category results,
  `ExactPairing.ofFaithful`, `exactPairingOfFaithful`,
  `hasRightDualOfEquivalence`, and rigid functor-category material. They need
  an equivalence, faithful pairing lifts, or other different data. No match.
- `msearch.py ... loogle`: `CategoryTheory.MonoidalClosed,
  CategoryTheory.ExactPairing` returned zero hits.
- `msearch.py ... grep`: `reflect.*dual|dual.*reflect|jointly.*conservative`
  in `CategoryTheory/Monoidal` returned zero hits.
- `msearch.py ... leansearch`: the same natural-language statement returned
  `Functor.Monoidal.ofBifunctor`, cartesian `MonoidalClosedFunctor`,
  reflection and symmetry transfer declarations; no detection theorem.
  Read Closed/Functor.lean: its closed-functor API is cartesian-specific.
- `rg` over upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for jointly conservative, dualizable locality,
  dual reflection and the proposed declaration name found geometric
  conservative-functor applications and internal-Hom comparisons only.
  The project consumer `CondensedLisseProEtaleLocality.lean` mentions the
  present node as a proof input but does not already state this generic lemma.
  Searching upstream for the item id found no declaration. No duplicate found.
- Read the Mathlib signatures identified by the node's existing searches:
  Closed/Basic.lean, Closed/Functor.lean, Rigid/Basic.lean, monoidal Functor.lean,
  Braided/Basic.lean and Adjunction/Unique.lean. Existing notions are reused;
  no private copy, local notation, local instance or helper is introduced.

Validation: `scompile.py NP lem-zl-dualizable-jointly-conservative-locality
lean/Sheaf/CategoryTheory/DualizableJointlyConservativeLocality.lean` passed for
both its sandbox and library-name compilation with no diagnostics. The first
compile exposed missing parentheses around functor-object expressions in β;
those syntax errors were repaired. Every binder/universe is explicit.

## Second reading by NP

Author self-check, under the dispatcher's direct-delivery instructions; the
maintainer supplies the independent reading. Reopened the node and final module
and matched every hypothesis and conclusion above. Checked that h is natural
in both arguments, that the symmetry appears on the correct side for each
transpose, that hTranspose uses μ A B rather than μ B A, and that the exact
pairing orientation is evaluation E ⊗ K and coevaluation K ⊗ E. Checked empty
and infinite index types remain allowed and conservativity is joint only.
No mathematical mismatch or statement change was found. The only compile
repair added parentheses to the target braiding's object arguments.
