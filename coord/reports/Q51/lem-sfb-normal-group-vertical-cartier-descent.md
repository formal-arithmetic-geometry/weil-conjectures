## Worker report

The item is now stated as `AlgebraicGeometry.Scheme.normal_group_vertical_cartier_descent`
in `Sheaf.AlgebraicGeometry.NormalGroupVerticalCartierDescent`. Its proof is `sorry`.
The supporting definition module contains real data only; it has no postponed theorem.
No mathematical statement, proof step, or proof dependency of the item was changed.
Its statement dependencies gain the new definition node described below.

The inherited BLOCKED ending concerned the accepted stage-1 split. The live queue lists
this item at stage 2 and its Lean record is absent. Q14's PASS reviewed its six-step
mathematical split, not a Lean declaration. There was no repair note for this item and
no existing sandbox module to recover. This delivery preserves that accepted split.

Hypothesis and clause correspondence:

- The base scheme is `S : Scheme.{u}`. `[IsIntegral S]` supplies integrality and
  nonemptiness; `[IsLocallyNoetherian S]` supplies local Noetherianity. The normality
  assumption `hS` requires `IsIntegrallyClosed` for every structure-sheaf stalk.
  Together with integrality this is exactly an integrally closed domain at every point.
- `G : Over S` retains both the total scheme `G.left` and the structural morphism
  `G.hom`. `[GrpObj G]` supplies addition, inverse, identity and their diagrams over S;
  `[IsCommMonObj G]` supplies commutativity. These are Mathlib notions, not a replacement
  package of laws. The identity section is the composite of the unique terminal-object
  isomorphism `Over.mkIdTerminal.uniqueUpToIso isTerminalTensorUnit` with `MonObj.one`,
  with its actual underlying scheme map. `(X := S)` merely helps elaboration unfold
  the source of this composite; no isomorphism or section is an additional hypothesis.
- `[Smooth G.hom]`, `[IsSeparated G.hom]`, `[LocallyOfFinitePresentation G.hom]` and
  `[QuasiCompact G.hom]` express smooth, separated, finite presentation. Separatedness
  is the closed immersion of the diagonal and implies quasi-separatedness, completing
  the node's finite-presentation condition. `[GeometricallyConnected G.hom]` is the
  condition that all field-valued base changes have connected total space.
- `U : S.Opens` and `hU : Dense (U : Set S)` are exactly a dense open subscheme.
  Its inverse image under `G.hom` is the underlying open of `G ×_S U`, so the conclusion
  `Dense (G.hom ⁻¹' (U : Set S))` is exactly the required density of G_U.
- The first conclusion `IsIntegral G.left` and the next stalkwise conjunction of
  `IsDomain` and `IsIntegrallyClosed` give normal integral G. The following universal
  `[IsIntegral G.left]` binder permits using that result in the remaining types without
  a hidden `let` or `have`; it adds no hypothesis to the theorem. There are no universe
  equalities or restrictions on the base field, dimension, or characteristic.
- `D : IntegralCartierDivisor G.left` denotes local nonzero rational equations modulo
  local regular units. It is not an effective Cartier divisor and not a Weil divisor.
  `integralCartierSupport D ⊆ (G.hom ⁻¹' (U : Set S))ᶜ` is precisely the support condition.
- The existential `E` is identified by `integralCartierPullback? e D = some E`, which
  asserts that the canonical partial pullback is defined and gives E. Its definition
  checks actual local fractions a/b with both their images nonzero; it does not assume
  a function-field map along the nondominant identity. The subsequent clauses assert
  support in S minus U and `integralCartierPullback? G.hom E = some D`, literally the
  claimed identity D = p*(e*D). The last implication is the zero-pullback consequence.
- For every `L : G.left.Modules` with `[L.IsInvertible]`, the binder `s` is the actual
  generic stalk and the explicit hypothesis `s ≠ 0` is a nonzero rational section.
  `HasIntegralCartierDivisor L s D` says that the rational coefficient in a regular
  stalk generator represents the Cartier class at every point. The unique existence
  assertion states that these coefficients define its Cartier divisor. Its final
  equivalence says that s extends to a global regular section generating all stalks
  if and only if this divisor is zero.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom.stalkMap`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `LocallyOfFiniteType.isLocallyNoetherian` is also the recorded proof input.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` for the normal-domain condition. No second normal-ring predicate is made.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and its flatness instance.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and the canonical
  `Scheme.Opens` presentation of an open subscheme.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded module-pullback
  interface. This is imported publicly; Cartier pullback is distinct from module pullback.
- `Mathlib.CategoryTheory.Monoidal.Grp` and `.Mon`: `GrpObj`, `IsCommMonObj`, `MonObj.one`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the integral-scheme clause reuses
  `Scheme.functionField`, the Mathlib generic stalk, and its stalk-to-function-field algebra.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`: reuses the Mathlib module-stalk
  carrier and scalar action, with `TopCat.Presheaf.stalkSpecializes` and `germ`.
- The already stated proof input
  `WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore`
  is imported privately, as is `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` for
  `Module.FaithfullyFlat.of_flat_of_isLocalHom` and faithful-flat spectrum surjectivity.
  The fibre-normal-integrality and local-generic-unit-factorization proof nodes currently
  have no recorded declarations, so their module imports cannot yet be named.

Edge cases checked before drafting: the empty base is excluded exactly by integrality;
G is nonempty because it has an identity over nonempty S. The dense open can be all S,
in which case only the zero vertical divisor occurs. It cannot be empty. Zero divisors,
identity group schemes, field bases, DVR bases, and normal nonregular bases are included.
The line need not have a global frame: the coefficient predicate uses stalk generators.
The section must be nonzero, precisely as in the node. Its regular extension is required
to generate every stalk, not merely to be regular. An arbitrary rational equation may
have zero denominator along the identity; the pullback predicate explicitly excludes
such a presentation and asks for another valid Cartier presentation. All schemes and
field/stalk types use their existing common universe u; no smaller test universe occurs.

Searches: `msearch.py leanfinder` on vertical Cartier descent returned normalization and
rational-map declarations, none with this statement. `msearch.py loogle` with
`AlgebraicGeometry.Scheme, CartierDivisor` returned unknown identifier / no hits.
`msearch.py grep` for `CartierDivisor|RationalSection` in Mathlib AlgebraicGeometry found
no hits. `msearch.py leansearch` on local Cartier equations returned structure-sheaf
localizations, analytic divisors, and rational maps, none supplying this interface.
Additional semantic searches and project/DAG rg searches are recorded verbatim in the
new node's mathlib_searches. `tools/blueprint_refs.py search Cartier` and ancestor lookup
were also read: the ancestor is null, as in the item's own blueprint record.
The item-id search in upstream WeilConjectures found no declaration.

The local Stacks source 0BD7 was read, including its local generic-unit factorization
and integral-fibre comparison. The final local-frame argument uses the node's explicit
Cartier definition and Stacks 01X5. Source-reference issue in the inherited split:
its proof-step citation calls 0B8Z a Cartier definition, but the local tag table identifies
0B8Z as varieties-lemma-general-degree-g-line-bundle. The new module does not repeat that
incorrect tag: it cites the node's actual local-equation definition and 01X5. This is a
bibliographic fault only, not a mathematical statement change. No statement is disputed.

## New nodes

`def-sfb-integral-cartier-divisor` supplies the missing integral-scheme Cartier interface:
a divisor is an intrinsically equal locally representable family of stalk cosets, its
support and zero, the canonical partial pullback characterized by actual fraction
pullback, and generic-stalk section coefficients and invertible regular extensions.
The coset is its actual subset f·O_x^× of K(X). This avoids postponed quotient relation
proofs, redundant chosen atlases and any hollow data. The partial map uses a decidable
unique-existence test and chooses its uniquely specified value; it relies on no sorry.
All its notions are defined by ordinary functions, subtypes, existential predicates and
actual stalk maps. Its source is the Cartier definition explicitly supplied in the item,
with rational-function and section interpretation from Stacks 01X5 and the item's 0BD7
proof. Search outputs are recorded in the new node.

The existing `RationalSectionDivisor` is restricted to smooth curves over algebraically
closed fields and constructs Weil divisors. `SpaceDivisorDefinitions` uses an algebraic
space small étale model and meromorphic module sections; its pullback module requires
flat maps and does not supply this partial pullback along an identity section. None
provides the required integral-scheme signature. The construction here has no new
scheme, function field, module category, stalk, or invertibility predicate. The new node
cites and imports their recorded owning modules. No dependency record is repaired.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
