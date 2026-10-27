## Worker report

The module `Sheaf.AlgebraicGeometry.DMGeometricInertiaTrivial` states
`AlgebraicGeometry.dm_geometric_inertia_trivial`. Its only proof is `sorry`.
It defines no new notions and makes no change to the natural-language statement,
statement dependencies, proof or proof dependencies.

The NF merge recorded in the live node was its stage-1 split, not a stage-2
statement: the node has `reviewed` but has neither `lean` nor `reviewed_lean`.
The initial sandbox contained no delivery module or node. This packet supplies
its first Lean statement, rather than re-delivering the unchanged stage-1 split.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`. The stack over S is the arbitrary total
  category `F : BasedCategory.{v, w} (Over S)`, retaining the actual objects,
  arrows, projection and fibre categories. Its object and arrow universes are
  explicitly bound independently of the scheme universe.
- The Deligne--Mumford hypothesis is `hF : IsDeligneMumfordModuliStack F`, using
  exactly the convention of `def-sfb-stable-pointed-moduli-groupoids`. I read its
  entire definition, including `IsModuliStack`, `IsFibredInGroupoids`,
  `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`, `SpaceMapIsEtale` and
  `SpaceMapIsSurjective`. It includes stack descent, representability of the
  diagonal by algebraic spaces, and a surjective etale scheme atlas tested on
  the actual space base changes. No stronger diagonal or separatedness
  assumption is added.
- Every algebraically closed field is quantified as
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]`. This is the size convention of
  the recorded dependency's geometric-field tests: `Spec (.of Ω)` is a scheme
  in the same universe as S. There is no requirement that Ω be algebraic over
  a specified ground field, nor any characteristic restriction.
- Every morphism `Spec Ω → S` is `a : Spec (.of Ω) ⟶ S`.
- Every object in the fibre over that morphism is
  `x : Functor.Fiber F.p (Over.mk a)`. I read Mathlib's fibre definition: its
  arrows are exactly the total-category arrows projecting to the identity.
- Triviality of its automorphism group is `(α : x ⟶ x), α = 𝟙 x`.
  Under `hF`, F is fibred in groupoids, so every fibre arrow is invertible.
  Thus quantifying over endomorphisms is exactly quantifying over
  automorphisms; it adds no assumption beyond the stated hypothesis.
- The algebraic space over S is `E : AlgebraicSpace S`. I read the recorded
  definition: this is an fppf sheaf with representable diagonal and a
  representable surjective etale scheme atlas, rather than a scheme or a
  sheaf without an algebraic-space condition.
- Its discrete groupoid of points is the existing `discreteModuli E.obj.obj`.
  I read this definition: its objects over T are natural transformations
  `h_T → E`, identified with E(T) by Yoneda. The comma projection has discrete
  fibres; neither a second category of elements nor a quotient copy is added.
- Natural equivalence over `Sch/S` is the existential
  `e : BasedFunctor (discreteModuli E.obj.obj) F` with
  `e.toFunctor.IsEquivalence`. A based functor commutes with the projections
  to the base by its `w` field. This is the same equivalence formulation as
  the dependency's `IsRepresentedByScheme`, with an algebraic space's
  presheaf replacing a scheme's Yoneda presheaf. Choosing the displayed
  direction does not change the symmetric equivalence assertion.
- The final conjunction
  `∀ (T : Over S) (x : Functor.Fiber F.p T) (α : x ⟶ x), α = 𝟙 x`
  quantifies over every S-scheme and every one of its fibre objects. There is
  no reducedness, affineness, field-valuedness or finite-type restriction.

Dependency declarations used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; signatures and docstrings read.
- `def-sfb-stable-pointed-moduli-groupoids`:
  `CategoryTheory.IsDeligneMumfordModuliStack` and
  `CategoryTheory.discreteModuli` (and their underlying predicates),
  `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`; full definitions
  and source docstrings read. `BasedCategory`, `BasedFunctor` and
  `Functor.Fiber` are the Mathlib structures that this interface uses.
- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, from its
  `mathlib_match`; full class signature and documentation read.
- `def-weil-algebraic-closure`: `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, as explicitly named in the
  dependency's `mathlib_match`. Algebraically closed fields, rather than
  the particular construction `AlgebraicClosure K`, occur in the statement.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`; its fppf sheaf, representable
  diagonal and atlas definitions read in full.

The proof-only imports are the recorded modules for algebraic closures,
geometric points and open immersions:
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
`Mathlib.AlgebraicGeometry.ResidueField`, and
`Mathlib.AlgebraicGeometry.OpenImmersion`. The three other proof dependencies
`lem-sfb-dm-isom-space-unramified`, `lem-sfb-unramified-space-open-diagonal`
and `lem-sfb-etale-sheaf-space-atlas-bootstrap` have no recorded Lean module
or Mathlib match in the read clone, and supply no notions needed to type this
statement. They remain in `proof_deps`, and their modules can be added by
the maintainer when stated. No new dependent theorem is needed to state
this item.

I read Stacks algebraic.tex, lemma-algebraic-stack-no-automorphisms (045H)
and proposition-algebraic-stack-no-automorphisms (04SZ), as well as
spaces-morphisms.tex, lemma-diagonal-unramified-morphism (05W1).
The declaration docstring carries all six steps of the already reviewed
proof split: unramified Isom space; open equalizer of the automorphism and
identity; all points in the equalizer using algebraic closures of residue
fields; effective descent for isomorphism classes; transfer of the atlas
with unique isomorphisms identifying ordinary and 2-fibre products; and
the etale-to-fppf algebraic-space bootstrap.

Edge cases checked before writing:

- Nonreduced T is included in the final universal quantifier. The open
  equalizer argument is scheme-theoretic, not an assertion that arbitrary
  maps agreeing on geometric points must agree.
- Empty T is included; the unique open subset containing all its points
  is the whole empty scheme, so the same argument applies.
- Empty geometric fibres make the object quantifier vacuous on that
  fibre; the assertion does not require a chosen geometric object.
- The empty algebraic space is allowed as E when the stack has no objects
  on nonempty schemes. No nonemptiness hypothesis is imposed on S or F.
- Every characteristic is allowed, and no tameness or prime-order
  restriction occurs. The DM hypothesis supplies the unramified Isom
  space that is essential for the passage to nonreduced tests.
- General algebraic spaces, including those not represented by a scheme,
  are allowed as the conclusion.

Searches for an existing declaration (all performed before writing):

- `msearch.py leanfinder`: "A Deligne Mumford stack with trivial geometric
  stabilizers is naturally equivalent to an algebraic space". Eight
  irrelevant sheafed-space/open-immersion/stalk-isomorphism hits; no match.
- `msearch.py loogle`: `"IsDeligneMumfordModuliStack", "AlgebraicSpace"`.
  Zero hits.
- `msearch.py leansearch`: "A Deligne Mumford stack with trivial
  automorphism groups over every algebraically closed field is an
  algebraic space". Eight scheme/open-immersion/formal-unramifiedness
  hits; none states the stack result.
- `msearch.py grep`:
  `IsDeligneMumfordModuliStack|[Dd]eligne.?[Mm]umford|trivialInertia|geometric.*stabiliz`.
  Zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for geometric inertia,
  trivial inertia, geometric stabilizers, and
  `IsDeligneMumfordModuliStack`: upstream hits concern Galois inertia,
  not stacks. Sheaf hits include the DM definition, the unpointed coarse
  moduli statement, and the proof docstring of smooth-curve abelian level
  rigidification, which cites this item but does not state it.
- Literal item-id search in `lean/WeilConjectures`: no hits.

No statement correction, new definition node, dependency-interface repair,
or STATEMENT-DISPUTED issue is needed.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
