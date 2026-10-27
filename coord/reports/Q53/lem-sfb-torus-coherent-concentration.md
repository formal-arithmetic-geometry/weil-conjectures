## Worker report

The delivery states `AlgebraicGeometry.EquivariantCoherent.torus_coherent_concentration`
in `Sheaf.AlgebraicGeometry.TorusCoherentConcentration`. Its sole theorem proof is
`sorry`. The helper module `Sheaf.AlgebraicGeometry.TorusCoherentLocalizationData`
contains four real definitions, with no postponed data or new theorem. The item's
natural-language statement, proof and proof dependencies are unchanged. Its
statement dependencies gain the landed definitions actually used and the new
localization definition node.

Hypothesis and clause correspondence:

- The field is `(F : Type u) [Field F]`; algebraic closedness is `[IsAlgClosed F]`.
  No characteristic or characteristic-zero instance occurs.
- The affine finite-type group scheme is `T : Grp (Over (Spec (.of F)))`, with
  `[IsAffine T.X.left]`, `[LocallyOfFiniteType T.X.hom]` and
  `[QuasiCompact T.X.hom]`. These are exactly affine and finite type, not a
  finite or reduced group assumption. The internal `GrpObj` is supplied by `T.grp`.
- The splitting is `(r : ℕ) (split : T ≅ MultiplicativeType.splitTorus F r)`.
  It is an isomorphism of group schemes. The rank may be zero; there is no
  chosen rational point or dense cyclic subgroup.
- The scheme over the field is `Y : Over (Spec (.of F))`; its algebraic action is
  `[ModObj T.X Y]`. Smoothness and projectivity are `[Smooth Y.hom]` and
  `[IsProjective Y.hom]`, using the node's H-projective convention.
- The fixed closed subscheme is `W : Over (Spec (.of F))` and
  `(i : W ⟶ Y) [IsClosedImmersion i.left]`. The hypothesis `hfixed` is the
  representing condition: an A-valued point factors through i if and only if,
  for every F-algebra B, every algebra extension map A → B and every t in T(B),
  its base extension is fixed. Factorization is unique because i is a closed
  immersion. This includes nonreduced test algebras and identity extensions.
  Test algebras have the same universe u as F and Scheme.{u}, as in the landed
  `torus_fixed_scheme_smooth` interface; no independently smaller universe is used.
- `[ModObj T.X W] [IsModHom T.X i]` record the induced invariant action and
  equivariance of this inclusion. They do not impose a new geometric condition:
  the representing fixed subfunctor has its canonical trivial action, and the
  closed immersion forces any compatible action to be that induced action.
- Coherent linearized modules are the existing `EquivariantCoherent.Coherent D`.
  They use `RingedSpace.IsCoherent`, hence finite type and finite-type kernels,
  and the existing `Scheme.GroupoidModule` descent isomorphism, identity and
  cocycle laws. `DY` and `DW` are coordinate-normalized presentations of the
  actual action groupoids, not arbitrary actions. They are theorem witnesses,
  not additional hypotheses.
- The integral abelian group is the existing `GZero D`, the free abelian group
  on those coherent objects modulo equivariant isomorphism and short exact
  sequence relations. No rational coefficients are introduced.
- Rational representations and R(G) in the introductory terminology are the
  imported `RationalModule`, `RepresentationGZero`, `IsRepresentationRing` and
  `IsRepresentationAction`: finite-dimensional coordinate comodules, counital
  and coassociative, with multiplication and associated bundles specified by
  the given coactions. No replacement notion is defined here. The conclusion
  specifically uses the character action stipulated by the node.
- The actual character group `X = Hom(T,G_m)` is
  `TrivialTorusCoherent.Character T = Additive (T ⟶ Grp.mk G_m)`.
  Its addition is multiplication of group-scheme characters. The existing ring
  `CharacterRing T = AddMonoidAlgebra ℤ (Character T)` has basis
  `AddMonoidAlgebra.single χ 1`, so multiplication is exactly e^χ e^ψ = e^(χ+ψ).
- `TorusLocalization.IsCharacterTwist χ M N` identifies the underlying sheaves
  by e and imposes `p*e ; beta_M.inv ; χ = beta_N.inv ; a*e` on T × Y.
  Thus it multiplies the forward fibre action by χ(t), with the specified sign.
  `CharacterAction D` is an actual module structure on the existing integral
  quotient, requires existence of every twist representative, and identifies
  scalar multiplication by e^χ with every such representative's class.
  The theorem supplies both module structures rather than assuming them.
- `eulerFactors T` is precisely `Submonoid.closure` of
  `{1 - AddMonoidAlgebra.single χ 1 | χ ≠ 0}`; the closure includes 1.
  `Localization (eulerFactors T)` is R_Sigma, with integral coefficients.
- Unfolding `IsLocalizedClosedPushforwardIso` gives an R-linear `push` on the
  two actual GZero quotients. It asserts that every source sheaf has an
  equivariant ordinary pushforward representative and pins `push [N] = [M]`
  for EVERY representative with `IsPushforward i N M`. That predicate uses the
  normalized tensor-pullback adjunction: its adjoint is an isomorphism to the
  ordinary sheaf pushforward and its counit intertwines the descent actions.
  Thus the map is fixed on all generators, not an arbitrary map between groups.
- The final clause is `Function.Bijective
  (push.baseChange (Localization (eulerFactors T)))`.
  Mathlib's `LinearMap.baseChange` is the R_Sigma-linear map
  id ⊗ push : R_Sigma ⊗_R GZero(W) → R_Sigma ⊗_R GZero(Y).
  By the canonical tensor commutor this is precisely the node's
  GZero(-) ⊗_R R_Sigma map. Bijectivity of this linear map is exactly its being
  an isomorphism of localized R-modules (also R_Sigma-modules).

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp` and `.Cartesian.Grp`: `GrpObj`, `Grp`,
  the group and commutative group structures on point/Hom sets
  (def-sc-group-scheme). `Grp (Over (Spec (.of F)))` is its stated specialization.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms
  (def-pc-scheme). `Over` records actual structure maps over F.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes
  `RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent`;
  the finite-type-kernel definition is used by `Coherent` (pqf-def-coherent).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the dependency's
  `AlgebraicClosure` in `.AlgebraicClosure` and `IsAlgClosure` were also read.
  The node asks here for an algebraically closed F, not a chosen extension.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (def-sbc-smooth-morphisms).
- The convention node def-pc-morphism-conventions points to
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective.IsProjective`
  (declaration namespace `AlgebraicGeometry.IsProjective`); its full source
  factorization definition and properness instance were read and used.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.splitTorus`, whose recursive product includes rank zero.
- `Sheaf.AlgebraicGeometry.TrivialTorusCoherentData`:
  `TrivialTorusCoherent.Character`, `.CharacterRing`, `.characterValue`;
  `.multiplicativeCommMonObj` supplies commutative multiplication of characters.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGZero`:
  `ActionGroupoidModel`, `Coherent`, `GZero`, `classOf`, `underlying`,
  `source`, `target`, `linearization`, `IsPushforward`.
- `Sheaf.AlgebraicGeometry.RationalRepresentationGZero`:
  `RationalModule`, `RepresentationGZero`, `IsRepresentationRing`,
  `IsRepresentationAction`, the introductory rational representation terminology.
- The new definition node provides `eulerFactors`, `IsCharacterTwist`,
  `CharacterAction`, `IsLocalizedClosedPushforwardIso`.
- Plain proof imports are the recorded projective-proper module
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, and
  `Sheaf.AlgebraicGeometry.EquivariantRegularSelfIntersection`.
  The localization-sequence, nonfixed-complement-annihilation and fixed-Euler-unit
  proof nodes have no Lean records on the read base, so have no proof import yet.
  They are not needed to type this statement and have not been restated.

Edge cases checked before writing and again against the final signature:
rank zero makes X zero and the generating set empty, so Sigma is {1} and the
represented fixed locus is all of Y; the asserted map is the identity.
Empty Y and empty W are not excluded by any Nonempty, point, positive dimension
or positive rank hypothesis. Coherent sheaves on the empty scheme give the zero
Grothendieck group. For a trivial action, W = Y; twisting, including the zero
character, has its ordinary meaning. The generator of Sigma excludes exactly
χ = 0, not torsion characters or any characteristic. The fixed-point test includes
all algebra extensions, not only F-points; nilpotent test algebras are included.
The inverse-beta twist equation was checked on the trivial line of weight χ:
its forward action is χ, not χ inverse. No claim that a projective scheme is
itself affine, and no invariant affine cover hypothesis, occurs.

Searches:

- `msearch.py ... leanfinder "Integral concentration for torus equivariant coherent
  Grothendieck groups after inverting nontrivial character Euler factors"`:
  eight analytic torus-integral and L-function results, no equivariant G-theory.
- `msearch.py ... leansearch "Character twisting action on equivariant coherent
  Grothendieck group and localization at 1 minus character"`: eight results,
  CharacterModule.congr, CharacterModule, modularCyclotomicCharacter.toFun_spec',
  FDRep.scalar_product_char_eq_finrank_equivariant, FDRep.char_tensor,
  MulChar.commGroup, Algebra.GrothendieckGroup.instInv, MulChar.inv_apply_eq_inv'.
  These are Pontryagin character modules, finite group representations or ordinary
  abstract characters, not general-action coherent character twists.
- `msearch.py ... loogle "LocalizedModule, AddMonoidAlgebra"`: zero hits.
- `msearch.py ... grep
  "equivariant.*(concentration|Grothendieck)|torus.*concentration"`: zero hits.
  Exact outputs of these three searches are stored in the new node's searches.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for torus, equivariant
  coherence, linearization, fixed subschemes and Grothendieck groups found the
  reused Q60 quotient and rational representation modules and Q35 character data.
  Literal item-id search in `lean/WeilConjectures` found no statement.
- `rg` for `IsCharacterTwist|IsLocalizedClosedPushforwardIso|eulerFactors` in both
  trees and DAG found no such geometric definitions; the only eulerFactors hits
  were unrelated analytic Weil-group L-functions. CoherentGroupPresentation.IsTwist
  is restricted to a trivial base action, so it cannot state twists on arbitrary Y.
- `tools/blueprint_refs.py search` for "character twist", "torus coherent
  concentration" and "torus coherent localization": zero matching blueprint nodes.
  `ancestor` returned None, matching the existing item's blueprint ancestry.

Source check: read the local Milne PDF, printed p.480 (PDF page 492). Theorem
22.50 cites Nielsen and Iversen for its numerical formula; the DAG explicitly
labels concentration as an agent-supplied prerequisite and does not attribute
its proof to Milne. No statement correction is needed. No STATEMENT-DISPUTED flag.
The currently withdrawn CompactObject example contains no declarations; the module
mode/header, public imports and docstrings follow the active stage-2 convention.

Validation: both delivered files compile individually, in dependency order, via
`scompile.py Q53 lem-sfb-torus-coherent-concentration <helper> <item>` against
current server sources, with no errors or warnings. The wrapper reported a local
cache space error, then its authorized server confirmation succeeded (2.5 s and
2.2 s respectively); no compiler limit was changed and no cache was modified.

## New nodes

`def-sfb-torus-coherent-localization-data` defines the Euler-factor multiplicative
subset, a general-action character twist, the normalized actual character-ring
module structure on the existing GZero, and the property that normalized ordinary
closed pushforward becomes bijective after extension of scalars. Its source is
the integral concentration node's own explicit conventions, attached to Milne,
Section 22d, Theorem 22.50, printed p.480, and Stacks Tag 03LF for descent.
The searches above found the constituent character ring and equivariant quotient,
which are reused; the missing part is their general-action character twist and
localized closed-pushforward interface. The node has its own module, no sorry,
no redefinition of a character group or Grothendieck group, and is cited by the
item. `IsLocalizedClosedPushforwardIso` is a real proposition defined from the
normalized map and Mathlib scalar extension, not an assumed concentration axiom.

## Second reading by Q53

This is the author's final rereading, not an independent second worker; the
assignment explicitly prohibits starting agents and assigns independent review
to the maintainer. Reopened the node, both final modules, the exact coherent
quotient/linearization/adjunction definitions and the character-ring definitions.
The beta inverse gives the correct forward weight sign, all character twists
have representatives, and the pushforward is normalized on every representative,
so none of these predicates can be satisfied by an empty implication on all
classes. The localized map is R_Sigma-linear by construction, with integral
coefficients. The only implementation correction was enabling the existing
`CategoryTheory.MonObj` scoped instances needed for Hom(T,G_m) to be a commutative
group; no mathematical hypothesis or clause changed. No mismatch was found in
the final hypothesis/ clause comparison above.
