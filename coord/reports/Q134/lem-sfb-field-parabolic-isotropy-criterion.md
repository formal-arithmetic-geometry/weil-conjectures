## Worker report

The delivery states `AlgebraicGeometry.exists_proper_minimalParabolic_of_noncentral_splitTorus`
in `Sheaf.AlgebraicGeometry.GroupScheme.FieldParabolicIsotropyCriterion`, with one
`sorry`, and supplies the missing rational-parabolic terminology in the new definition
node `def-sfb-parabolic-subgroup`. No statement correction or dependency repair is needed.
The item's original statement, proof, and proof dependencies are unchanged. Its statement
dependencies gain the new definition and the already recorded split-torus definition node.

Clause-by-clause rendering of the item:

- Any field k: `{k : Type u} [Field k]`, with no perfection, characteristic, infinitude,
  algebraic-closedness, or separable-closedness hypothesis.
- G and T are group schemes over k: `G T : Grp (Over (Spec (.of k)))`. The bundled group
  objects supply actual multiplication, inverse and identity morphisms. `i : T ⟶ G`
  is a group homomorphism, rather than an arbitrary scheme map.
- G reductive: `hG : ReductiveTorusCentralizer.IsReductive G`. Its recorded definition
  expands to affine finite type, smoothness, connectedness after algebraic closure,
  and triviality of every smooth connected normal closed unipotent subgroup after
  that extension. `SolvableGroupStructure.IsAlgebraic` means affine, locally finite
  type and quasi-compact; `IsUnipotent` includes smoothness and a faithful closed
  finite-dimensional matrix embedding with nilpotent g minus identity on every
  algebraically closed extension. Thus none of the node's explanatory clauses
  about reductivity or unipotence is replaced by an abstract predicate parameter.
- Closed inclusion of T: `[IsClosedImmersion i.hom.hom.left]`. Since i is already a
  group homomorphism, a closed immersion is exactly a closed subgroup inclusion.
- Split torus, including rank zero: `hT : ∃ r : ℕ, Nonempty
  (T ≅ MultiplicativeType.splitTorus k r)`. The recorded splitTorus is the genuine
  finite product of the recorded multiplicative group, with the trivial group at zero.
- Noncentrality: `hnoncentral` existentially binds a commutative k-algebra A, a point
  `t : StandardGroupSchemes.affine k A ⟶ T.X`, and a point
  `g : StandardGroupSchemes.affine k A ⟶ G.X`, and asks for
  `¬ Commute (t ≫ i.hom.hom) g`. The scoped group law on Hom sets is the actual group
  scheme law. This is precisely tg ≠ gt, on arbitrary algebras, including nonreduced ones.
- Existence of a parabolic over the original field: the conclusion binds a group
  scheme P over Spec k and a group homomorphism `j : P ⟶ G`. Its first conjunct is
  `IsMinimalParabolicSubgroup j`, whose first conjunct is `IsParabolicSubgroup j`.
- Parabolic means a closed immersion, smooth structural map, connected scalar
  extension to the algebraic closure, and representation of the actual fppf
  right-coset sheaf by an X over k with `IsProper X.hom`, `LocallyOfFiniteType X.hom`
  and `QuasiCompact X.hom`. All these are explicit conjuncts in the new definition.
- The coset sheaf is constructed with real data: sheafification of the presheaf
  coequalizer of the projection and right action `(g,p) ↦ g i(p)`. Presheaf colimits
  are pointwise, so the equivalence classes are exactly right P(A)-cosets.
  The big fppf site's affine basis gives the stated algebra-site sheafification.
  Representation is a `Nonempty` isomorphism of its underlying presheaf with
  `uliftYoneda.obj X`; no representing object or arbitrary map is chosen from sorry.
- Minimality: every other parabolic `j : Q ⟶ G` and every factorization
  `f : Q ⟶ P` over G has `IsIso f`. This compares subgroup images in G and is
  precisely absence of a strictly smaller parabolic. It does not ask that the
  torus lie in the resulting minimal parabolic, which the item does not assert.
- Properness: `¬ IsIso j`. For a closed subgroup inclusion this says P ≠ G as a
  subgroup scheme, independently of the chosen isomorphic representative of P.
- The final sentence on finite and imperfect fields is retained by the unrestricted
  `[Field k]`; there are no extra assumptions on any field or test algebra.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`,
  and the group law on Hom sets. The specialization to schemes over Spec k and
  subgroup interpretation are documented in the recorded
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`; its source and full
  definition were read, including its existing `SolvableGroupStructure` predicates.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.splitTorus` and `MultiplicativeType.baseChange`; the former
  uses `StandardGroupSchemes.multiplicative` and the latter transports the group law
  along scheme pullback. `StandardGroupSchemes.affine` is the k-scheme Spec A.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; together
  with `QuasiCompact` this is exactly finite type in the recorded dependency.
- New definition module `Sheaf.AlgebraicGeometry.GroupScheme.ParabolicSubgroup`:
  `fppfRightCosetSheaf`, `IsParabolicSubgroup`, `IsMinimalParabolicSubgroup`.

The new definition also uses the existing definition-node interfaces:
`Smooth` (def-sbc-smooth-morphisms), `ConnectedSpace`
(def-weil-connected-scheme), `Scheme.fppfTopology` and its `.over` construction
(def-pc-fppf-site), and `CategoryTheory.presheafToSheaf`
(def-weil-pbc-sheafification). Their defining sources and the concrete-sheafification
instance used by the analogous additive quotient were read.

The proof plan in the theorem docstring contains all four original steps: choose a
noncentral coordinate cocharacter; obtain its projective parabolic quotient; prove
properness by killing the split-unipotent kernel after algebraic closure and faithfully
descending its centralizer ideal; choose a minimal closed support and use reduced-induced
closed-subscheme uniqueness. Imports for already recorded proof dependencies are plain
imports: `SmoothUnipotentExtension`, `ProjectiveImpliesProper`, the Mathlib finite-type,
prime-spectrum and topological Noetherian results, the upstream geometrically-reduced
module, and the recorded upstream reduced-induced-closed-subscheme module. Their
statements/docstrings were read. The cocharacter-geometry proof dependency has neither
a Lean record nor a Mathlib match in the read repository; no import can yet be supplied
for that proof dependency. It is not needed to type the present statement. No declaration
of that much larger theorem is assumed or fabricated in this delivery.

Edge cases checked before writing:

- Rank-zero split T is trivial and all its points commute: hnoncentral is impossible.
  We retain rank zero in the split hypothesis rather than adding r > 0.
- A torus G, including a split torus, has no noncentral torus. The theorem does not
  incorrectly infer a proper parabolic merely from a nontrivial central split torus.
- The trivial reductive group and anisotropic groups likewise fail the noncentral
  hypothesis. The whole G is allowed in the definition of parabolic and can be
  minimal for an anisotropic G; only the theorem's conclusion also requires properness.
- Over the zero test algebra the point groups are trivial, so this algebra cannot
  witness noncentrality. It remains an allowed test algebra. Nilpotent test algebras
  are also retained; noncentrality is not tested merely on k-points or geometric points.
- Finite and imperfect fields, positive characteristic and nonsplit reductive groups
  are all admitted. No Borel over k, splitness of G, or rational-point density is assumed.
- The empty scheme cannot be a group scheme over a field because of its unit section;
  ConnectedSpace includes nonemptiness and excludes no permitted subgroup.
- P and G have the same scheme-size universe; test algebras use that universe as in
  the recorded group-scheme interfaces. Sheafification values use Type (u + 1),
  large enough for the big site, using lifted Yoneda. There is no independent smaller
  universe making the test-algebra quantification vacuous. All variables/universes
  are explicitly bound and `autoImplicit` is false in both modules.

Searches:

1. `msearch.py ... leanfinder` with “A reductive group over a field containing a
   noncentral split torus has a proper minimal parabolic subgroup”: eight hits on
   modular cusps, root systems and Lie algebras, no group-scheme theorem.
2. `msearch.py ... loogle '"parabolic"'`: twelve hits on parabolic 2 by 2 matrix
   elements; no parabolic subgroup-scheme notion.
3. `msearch.py ... grep 'IsParabolic|parabolic.*[Ss]ubgroup|[Cc]oset[Ss]heaf'`:
   thirteen unrelated matrix/modular hits.
4. `msearch.py ... leansearch` with “Parabolic subgroup scheme defined by smooth
   geometrically connected closed subgroup with proper fppf coset sheaf quotient”:
   eight hits on ideal subschemes, topological closed subgroups and smoothness,
   no match. Exact returned JSON search records are in the new node's mathlib_searches.
5. `rg` of WeilConjectures and Sheaf for parabolic predicates and coset constructions:
   no general parabolic predicate; the additive-specialized quotient is not general.
   Existing `IsFppfGroupQuotient` requires a group quotient and normal kernel and
   cannot describe a general G/P. Existing StandardParabolicLeviCharts uses an inline
   coequalizer universal property in a theorem, not a reusable parabolic definition.
6. DAG definition-node search for parabolic/right cosets found only the normal-kernel
   group-quotient presentation (and an irrelevant diagonalizable-group hit).
   `tools/blueprint_refs.py search parabolic` returned zero blueprint nodes.
7. The prescribed source-ID search in lean/WeilConjectures returned no occurrence of
   lem-sfb-field-parabolic-isotropy-criterion. No matching existing statement was found.

Source checked in the local Milne PDF: printed pp.544--546, including the exact
noncentral-split-torus criterion of Proposition 25.2, and Definition 17.15 on p.356.
The current node already fixes the noncentrality issue in the prose surrounding
Milne's proof of Theorem 25.10. No further statement fault or dispute was found.

Validation: both files compiled in dependency order using the prescribed scompile.py
server wrapper, both under sandbox and actual library module names. No errors or
unexpected warnings were reported. The parabolic module contains only real-data
constructions and Prop definitions; the theorem's sole proof is sorry.

## New nodes

`def-sfb-parabolic-subgroup` introduces the fppf right-coset sheaf, parabolic subgroup,
and minimal-parabolic predicate, in its own module. Source: Milne Definition 17.15,
p.356, Chapter 25(a), pp.544--546, and Definition 5.20/Proposition 5.25, pp.104--105.
The searches above show no existing definition node or declaration for this notion.
The group-quotient definition requires normality and cannot be substituted here.
Its fields cite the existing field, group-scheme, closed-immersion, smoothness,
connectedness, scalar-extension, properness, finite-type, fppf-site and sheafification
notions. No independent copy of any of those notions is introduced. The item directly
cites this new node, and the item gains the existing split-torus node as well.

## Second reading by Q134

A separate local reading of the written signatures against both node statements
confirmed every correspondence listed above. This is a second pass by the same worker;
no independent subagent was started, as required by the dispatch brief. The maintainer's
independent delivery review remains separate. The pass checked in particular that the
right-action coequalizer gives right cosets (not a normal group quotient), that
representation is by an actual lifted-Yoneda presheaf, that the quantified smaller
parabolics are in the ambient G, and that properness is separate from minimality.
It also checked the rank-zero and central-torus cases, the same-size test-algebra
quantification, and all original proof steps in the theorem docstring. The split-torus
module was made an explicit public import and its landed definition node was added to
stmt_deps. No mathematical mismatch or statement correction was found.
