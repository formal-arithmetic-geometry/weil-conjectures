## Worker report

Delivery: `lem-sfb-minimal-parabolic-split-centralizers`, group Q160, stage 2.
The module `Sheaf.AlgebraicGeometry.GroupScheme.MinimalParabolicSplitCentralizers`
states `AlgebraicGeometry.minimal_parabolic_split_centralizers`, with its sole
proof `sorry`. Its docstring gives the node's eight-step proof plan. The companion
module `Sheaf.AlgebraicGeometry.GroupScheme.RationalParabolic` gives two actual
Prop-valued definitions, with no postponed data or proof obligations. No statement
correction or dependency-module repair is needed.

Sources read: Milne, Algebraic Groups (2017), Definition 17.15, printed p.356;
Chapter 25(a), especially Theorem 25.1 p.544 and Theorem 25.6(b),(c), pp.545--546.
The author errata https://www.jmilne.org/math/Books/iagerrata.html, entry
“p.545 et seq.”, explicitly requires minimality in 25.6(b). The assigned node
already has that restriction and asks only existence of the conjugator. Its
statement, source, proof and proof dependencies are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary field is `{k : Type u} [Field k]`, with explicit universe `u`.
  There is no `PerfectField`, `Infinite`, characteristic or algebraic-closure
  assumption on k. All test algebras have the field's universe, as in the recorded
  centralizer and unipotence interfaces, so they cannot be smaller than k.
- The reductive k-group is `G : Grp (Over (Spec (.of k)))` and
  `hG : ReductiveTorusCentralizer.IsReductive G`. Reading that definition shows
  affine finite type (`SolvableGroupStructure.IsAlgebraic`), smoothness, connectedness
  after `AlgebraicClosure k`, and triviality of every smooth connected normal
  closed unipotent subgroup after that extension. Its unipotence is the recorded
  faithful finite-dimensional matrix condition, including all geometric points.
- The parabolic inclusion is `iP : P ⟶ G` with
  `hP : IsMinimalParabolicGroupScheme iP`. The new definition includes closedness,
  smoothness, geometric connectedness, and a proper represented right-coset quotient.
  It defines minimality by: for every closed inclusion `j : Q ⟶ P`, if `j ≫ iP`
  is parabolic in G then `IsIso j`. Thus “minimal” is among parabolics in G,
  not among parabolics in P, and no properness restriction on P is inserted.
- The two given tori are `S : Fin 2 → Grp ...`, with `iS : ∀ a, S a ⟶ P`.
  `hclosed` expresses closed subgroup inclusions, `hsplit` says each is isomorphic
  as a group scheme to `MultiplicativeType.splitTorus k r`, allowing r=0. The
  recorded split torus is the actual recursive product of the Laurent G_m scheme.
- `hmax` quantifies over every closed split torus `j : T ⟶ P` and every
  factorization `f : S a ⟶ T` with `f ≫ j = iS a`, requiring `IsIso f`.
  This is maximality under inclusion in P, not maximality in G or among all tori.
- The conclusion produces `U` and `iU : U ⟶ P` which is closed and normal,
  geometrically connected, and `SolvableGroupStructure.IsUnipotent U`. This last
  predicate includes smoothness and a closed faithful matrix representation.
  The following universal clause ranges over EVERY closed normal geometrically
  connected unipotent `N ⟶ P` and factors it through iU. It therefore specifies
  the largest subgroup R_u(P), not an arbitrary unipotent complement. Affineness
  and finite type follow from closedness in P, a closed subgroup of reductive G.
- The conclusion produces `L : Fin 2 → Grp ...` and `iL : ∀ a, L a ⟶ P`.
  Each is closed in P and reductive. Composing iL with iP also gives a closed
  subgroup of G. For EVERY commutative k-algebra A, the displayed equality
  `centralizerPoints (iS a ≫ iP) A = Set.range (...)` identifies its functor of
  points with exactly C_G(S_a). The existing `centralizerPoints` tests every map
  A→B and every S_a(B) point. No reducedness or rational-point-only shortcut occurs.
- `IsIso ((fst ... ≫ iU.hom.hom) * (snd ... ≫ (iL a).hom.hom))` says that the
  actual multiplication morphism U×_k L_a→P is an isomorphism of k-schemes.
  The tensor here is the cartesian tensor in Over(Spec k), hence the fibre product.
  The extra written-out existential c gives the restricted conjugation morphism
  L_a×U→U, with `c ≫ iU = l u l⁻¹`. Together with normality and the two group
  homomorphism inclusions, these clauses say precisely U semidirect L_a ≅ P.
  The semidirect multiplication transported along this multiplication isomorphism
  is (u,l)(u',l')=(u c(l,u'),ll'); its action is fixed by the displayed conjugation
  equation and closed inclusion, rather than an unspecified action or isomorphism.
- `u : 𝟙_ (Over (Spec (.of k))) ⟶ U.X` is a SINGLE k-rational point.
  `e : L 0 ≅ L 1` is an isomorphism of group schemes. The final equality on
  (L 0).X is `u (iL 0) u⁻¹ = e.hom ≫ iL 1`, where u is made constant by
  `toUnit`. Since e is an isomorphism, this is equality of the conjugate subgroup
  schemes, not merely containment or equality of their rational points. It also
  gives that equality inside G after composition with iP.

Recorded dependency declarations used (the full declarations and docstrings were
read in the source):

- `Field`, Mathlib.Algebra.Field.Defs, for def-weil-field.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, and its bundled
  `CategoryTheory.Grp`, for def-sc-group-scheme. The project specialization and
  group-scheme homomorphisms are documented in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` and
  `.centralizerPoints`, Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology.
  That module publicly supplies the existing IsUnipotent, splitTorus and baseChange
  interfaces through SolvableGroupStructure and ToriMultiplicativeType.
- `AlgebraicGeometry.IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion;
  `AlgebraicGeometry.IsProper`, Mathlib.AlgebraicGeometry.Morphisms.Proper;
  `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
  Properness supplies finite type, since universally closed implies quasi-compact.
- Existing subgroup and normal subgroup predicates, from
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs; Smooth, Flat and
  LocallyOfFinitePresentation from their Mathlib morphism modules; ConnectedSpace
  from Mathlib.Topology.Connected.Basic. No copies of these notions are introduced.
- Proof-only import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage,
  declaration `AlgebraicGeometry.affineGroupHom_exists_faithfullyFlat_closedImmersion`.
- Proof-only import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected,
  declaration `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_section`.
  The other nine proof dependencies have no recorded Lean declaration on the read
  base, so there is no additional proof module to import at this stage.

Edge cases checked: split rank zero and the trivial group; zero cocharacter and an
empty set of weight differences; P=G when no proper parabolic exists (U=1 and
L_0=L_1=G); the two tori being equal; finite fields and imperfect fields; positive
characteristic, including p=2; nonreduced test algebras and the zero test algebra.
Nothing excludes these. A parabolic quotient is nonempty because it has the
identity coset, but no extra nonemptiness hypothesis is imposed. The new definition
is meaningful with P=G and quotient Spec k. No disputed statement was found.

Searches run with the prescribed msearch.py wrapper:

- LeanFinder: “Centralizers of maximal split tori in a minimal parabolic are
  reductive Levi subgroups conjugate under the unipotent radical”: 8 hits, all
  Lie/abstract root-system results, no group-scheme match.
- Loogle: `"centralizer", "torus"`: 0 hits.
- Grep: `[Pp]arabolic|[Uu]nipotentRadical|[Mm]aximalSplitTorus`: 16 hits, matrix
  parabolic elements, modular forms and topology, no algebraic-group statement.
- LeanSearch: “A parabolic subgroup is a smooth geometrically connected closed
  subgroup with proper represented quotient”: 8 hits, headed by matrix parabolic
  elements and unrelated closed-subgroup/quotient declarations.
- LeanFinder: “Parabolic subgroup scheme minimal rational parabolic proper fppf
  quotient”: 8 unrelated rational-map/affine-space hits.
- Loogle: `"parabolic"`: 12 matrix-parabolic declarations, no rational parabolics.
- Grep: `IsParabolic|parabolic subgroup|[Pp]arabolic.*[Qq]uotient`: 13 hits,
  all matrix-parabolic declarations.
- Direct rg in Mathlib, lean/WeilConjectures and lean/Sheaf for
  `IsParabolicGroupScheme|IsMinimalParabolicGroupScheme|minimal_parabolic_split_centralizers`:
  no existing declaration. Direct searches for the item id and centralizer/split
  keywords find only existing centralizer predicates and other geometry theorems.
  dag/lean_names_upstream.json has no matching parabolic declaration.
- `rg -l parabolic dag/nodes/*/def-*.json`: no existing rational-parabolic definition.
  `python3 tools/blueprint_refs.py search parabolic`: 0 blueprint nodes match.
  `python3 tools/blueprint_refs.py ancestor <item>` returns ancestor None, inherited
  in the new node, with the item's full existing source route retained in place/via.

Validation: both files compiled individually via scompile.py in dependency order,
against the live server build, with no errors or warnings (apart from the permitted
sorry warning). Final library compile times: RationalParabolic 1.6 s,
MinimalParabolicSplitCentralizers 2.0 s. autoImplicit is explicitly false in both.

## New nodes

`def-sfb-rational-parabolic-subgroup` defines
`AlgebraicGeometry.IsParabolicGroupScheme` and
`AlgebraicGeometry.IsMinimalParabolicGroupScheme` in
Sheaf.AlgebraicGeometry.GroupScheme.RationalParabolic. It is the missing notion in
the item's hypothesis, sourced to Milne Definition 17.15 and Chapter 25(a).
The search results above and their actual msearch outputs are recorded in its
mathlib_searches. The existing cocharacter limit functors are not a definition of
arbitrary parabolics. The existing IsFppfGroupQuotient concerns a group quotient by
a specified normal kernel and has a group target; it cannot encode a nonnormal
parabolic right-coset quotient. No separate quotient construction is copied: the
new parabolic predicate directly specifies a scheme Q and its fppf coset projection.

The projection formulation is equivalent to the item’s fppf right-coset sheaf:
flat, surjective, locally finitely presented maps provide local sections by base
change, and the coset identity identifies their kernel pair. Thus the represented
fppf sheaf is the sheafification of A↦G(A)/P(A). Conversely the canonical projection
to a represented quotient by a smooth closed subgroup is its fppf torsor. In this
finite-type affine group setting it has exactly the properties used in the new
predicate. There is no assumption that P is normal, or Q a group scheme.

## Second reading by Q160

This is the dispatcher's requested author re-reading; the maintainer supplies the
independent review. I re-read the item JSON and both complete modules, and compared
all binders and conclusions using the correspondence above. Minimality quantifies
over parabolics in G; maximality quantifies over split tori in P. In particular,
neither field perfection nor ambient maximality of the tori was slipped in.
The radical universal property covers all normal smooth geometrically connected
unipotent subgroups, including over imperfect k; it is not just geometric maximality.
I checked the order of multiplication U then L and of conjugation u L u⁻¹.
The displayed IsIso applies to the multiplication morphism, not a homomorphism from
the direct-product group law. The initial draft wrote the product isomorphism with
normality; on re-reading I made the restricted conjugation action explicit by the
morphism c and its defining equation. Final compilation includes this adjustment.
I also added the recorded affine-image proof import, after auditing all proof nodes.
No item statement correction or further mismatch was found. Every declaration's
source/blueprint docstring, all 100-character limits and verbatim node signatures
were checked. No proofs were supplied and no data definition uses sorry.
