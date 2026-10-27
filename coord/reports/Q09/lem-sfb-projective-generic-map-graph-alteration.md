## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveGenericMapGraphAlteration` states
`AlgebraicGeometry.projective_generic_map_graph_alteration`. Its sole proof is `sorry`;
there are no new definitions, auxiliary postponed statements, or statement corrections.
The node is changed only in `lean`.

The correspondence with every hypothesis is as follows.

| Node | Lean |
| --- | --- |
| Field k | `k : Type u`, `[Field k]` |
| Integral scheme S over k | `S : Scheme.{u}`, `[IsIntegral S]`, `s : S ⟶ Spec (CommRingCat.of k)` |
| Separated and finite type over k | `[IsSeparated s]`, `[LocallyOfFiniteType s]`, `[QuasiCompact s]` |
| Generic point eta, function field K | `η : S`, `_hη : IsGenericPoint η Set.univ`, `[Field K]`, `eK : S.presheaf.stalk η ≅ CommRingCat.of K` |
| Finite separable L/K | `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[Algebra.IsSeparable K L]` |
| Finite surjection q:N to S | `q : N ⟶ S`, `[IsFinite q]`, `[Surjective q]` |
| N normal integral, finite type over k | `_hN : IsNormalScheme N`, `[LocallyOfFiniteType (q ≫ s)]`, `[QuasiCompact (q ≫ s)]` |
| j identifies the function field of N with L | `ηN`, `_hηN`, `eN : N.presheaf.stalk ηN ≅ CommRingCat.of L`, and `_hj : j = Spec.map eN.hom ≫ N.fromSpecStalk ηN` |
| This identification respects K and induces the given generic-fibre isomorphism | `_hgeneric : IsPullback j (Spec.map (CommRingCat.ofHom (algebraMap K L))) q (Spec.map eK.hom ≫ S.fromSpecStalk η)` |
| Projective finite-type k-scheme M | `p : M ⟶ Spec (CommRingCat.of k)`, `[IsHProjective p]`, `[LocallyOfFiniteType p]`, `[QuasiCompact p]` |
| k-morphism a:Spec L to M | `a` and `ha : a ≫ p = j ≫ (q ≫ s)` |
| Q=M times_k N and the graph point x | `pullback p (q ≫ s)` and `pullback.lift a j ha (IsLocalRing.closedPoint L)` |
| i:T to Q is the reduced induced closed subscheme of closure {x} | `T`, `i`, `[IsClosedImmersion i]`, `[IsReduced T]`, and `_hi : Set.range i = closure {…}` |

`IsNormalScheme N` is the existing definition, not a replacement: it is `IsIntegral N`
and, at every point, `IsDomain` and `IsIntegrallyClosed` for the stalk. The node states
this notion inline. Likewise the field structure on K is identified with the chosen
generic stalk through `eK`, rather than introducing an unrelated field. The induced
k-structure on L is the composite `j ≫ q ≫ s`, so `ha` is precisely the k-linearity
condition and does not impose an additional independent algebra structure.

The correspondence with every conclusion is as follows.

| Node | Lean |
| --- | --- |
| T integral | First conjunct `IsIntegral T` |
| Factorization through i | `∃ jT`, `jT ≫ i = pullback.lift a j ha` |
| jT is the generic-point map identifying k(T) with L | `∃ ηT, IsGenericPoint ηT Set.univ ∧ ∃ eT : T.presheaf.stalk ηT ≅ CommRingCat.of L, jT = Spec.map eT.hom ≫ T.fromSpecStalk ηT` |
| b:T to N is proper and surjective | `IsProper (i ≫ pullback.snd p (q ≫ s))` and `Surjective` of the same map |
| Canonical Spec L to T times_N Spec L is an isomorphism over L | `IsPullback jT (𝟙 (Spec (CommRingCat.of L))) (i ≫ pullback.snd p (q ≫ s)) j` |
| r=q composed with b proper and surjective | `IsProper` and `Surjective` of `i ≫ pullback.snd p (q ≫ s) ≫ q` |
| r finite type | `LocallyOfFiniteType` and `QuasiCompact` of that composite |
| Dense open V of S over which r is finite | `∃ V : S.Opens, Dense (V : Set S) ∧ IsFinite (r ∣_ V)`, with r expanded |
| Induced function-field extension is the prescribed L/K through jT | The generic-stalk isomorphism `eT`, its equation for `jT`, the factorization equation, and `_hgeneric` preserve the exact map `Spec L → Spec K` induced by `algebraMap K L` |
| m=pr_M composed with i, and m composed with jT=a | Final equation `jT ≫ (i ≫ pullback.fst p (q ≫ s)) = a` |

For clarity about the function-field clause: projection of the factorization equation
gives `jT ≫ (i ≫ pullback.snd p (q ≫ s)) = j`. Composing with q and using the
commutativity of `_hgeneric` gives
`jT ≫ (i ≫ pullback.snd p (q ≫ s) ≫ q) =
Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map eK.hom ≫ S.fromSpecStalk η`.
Together with the displayed generic-stalk descriptions of j and jT, this says that the
induced function-field map is exactly K to L. It is not just the existence of abstract
isomorphic fields. A Cartesian square with second edge the identity of Spec L says
that the particular comparison determined by jT and that identity is an isomorphism;
it therefore retains the requested compatibility over L.

Quantifying the reduced closure by its characterizing properties introduces no
arbitrary model assumption. Stacks 01J3 and the recorded
`Scheme.IdealSheafData.reduced_induced_closed_subscheme` state exactly existence and
unique isomorphism over Q of the reduced closed immersion with the given closed image.
Thus the theorem applies to the canonical vanishing-ideal model and to any representative
of the same closed subscheme. No choice of an unknown scheme or arbitrary map is used.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, including its composition,
  finite-implies-proper and base-change instances; `Morphisms.Separated`: `IsSeparated`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: imports the recorded
  `Scheme.functionFieldOfComponents` and Mathlib's generic-stalk `Scheme.functionField`.
  The arbitrary integral-scheme clause of `def-sc-function-field` is the generic stalk;
  using an explicit generic point avoids choosing a different representative.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift`; `IsPullback` expresses the two generic-fibre clauses.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, including uniqueness.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `WeilConjectures.AlgebraicGeometry.NormalScheme`: `IsNormalScheme` (existing notion
  of the node's inline normal-integral hypothesis).

The stated proof dependencies are imported without `public` when needed only for the
proof: `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`
(`hProjective_properness`),
`Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood`
(`Scheme.Hom.exists_dense_open_isFinite_of_finite_generic_fibers`),
`Mathlib.AlgebraicGeometry.Fiber` (`Scheme.Hom.fiber`),
`Mathlib.AlgebraicGeometry.Noetherian`, and
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`.
The remaining proof-dependency modules are already direct public imports, including
Mathlib's function-field and affine pullback APIs. The theorem docstring contains the
seven proof steps, including the tensor-product calculation that identifies the entire
generic fibre, with their DAG dependencies.

Edge cases checked before writing:

- Integral S is nonempty; the finite surjection and normal-integral hypothesis exclude
  empty N. The existence of a excludes empty M. No separate nonemptiness assumption
  on M or T is added; nonemptiness of the graph closure is a conclusion.
- Dimension zero S and N, L=K, and an identity q are admitted. In dimension zero the
  dense open can be all of S and the generic-fibre assertion becomes the field-point model.
- No positive dimension, characteristic restriction or algebraic closure is assumed.
  Finite separable extensions of any degree, including degree one, are admitted.
- Nilpotents in M or Q are allowed; only the specified graph closure T is reduced.
  Neither T normal nor the map r finite everywhere is asserted.
- All schemes and field spectra live in an arbitrary common universe u, as in the
  recorded scheme and fibre-product APIs; every variable and universe is explicit and
  `autoImplicit` is false. The finite extension is not confused with a finite-type
  algebra condition on a potentially transcendental field extension.
- `IsHProjective` is the finite projective-space embedding convention of the node,
  not an unrelated projectivity condition on a categorical object.

Searches (2026-10-24, full wrapper logs in the sandbox's `searches.jsonl`):

- `msearch.py … leanfinder`: "The reduced closure of a point in a projective scheme
  over an integral scheme preserves its function field and is a proper surjective
  generically finite alteration". Eight hits: rational-map/function-field interfaces,
  valuative properness, normalization. None states the graph-closure theorem.
- `msearch.py … loogle`: `"AlgebraicGeometry", "functionField"`. Twelve hits on the
  existing function-field definition and fraction-ring API; none supplies this result.
- `msearch.py … grep`: `graph|genericFiber|genericFibre|functionField`, subdirectory
  `AlgebraicGeometry`. Twenty-one hits, chiefly function fields and rational maps;
  no exact match.
- `msearch.py … leansearch`: "The reduced graph closure of a generic map to a projective
  scheme is proper surjective and preserves the function field". Eight hits on proper
  and dominant maps, rational maps and closed immersions, with no exact statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for graph alteration, generic graph,
  graph closure and the item id: related graph constructions and proof references,
  but no declaration stating this node. The proposed declaration name also has no hit
  in either root or `dag/lean_names_upstream.json`.
- `rg` for normal-scheme predicates found the existing `IsNormalScheme`; its full
  definition and owning node `def-sbc-normal-dominant-galois` were read and reused.
  No new notion or node was needed.

Sources opened: `literature/stacks-project/schemes.tex`,
`lemma-reduced-closed-subscheme` (01J3), and `morphisms.tex`,
`lemma-algebraic-residue-field-extension-closed-point-fibre` (01TE) and
`lemma-generically-finite` (02NW), including its quasi-compact/quasi-separated
hypotheses for (4). The node explicitly records that the whole graph statement is an
agent assembly, not a verbatim Stacks lemma. No fault or mathematical dispute was found.

Validation: `scompile.py Q09 lem-sfb-projective-generic-map-graph-alteration` compiled
the file both as a sandbox module and under its final library module name, with no
errors or warnings. The first compile's unqualified `closedPoint` was repaired to
`IsLocalRing.closedPoint` before this clean run. No local Lean build was run.

## Second reading by Q09

The dispatcher forbids starting another agent, so this is a second pass by the same
worker, not a claim of independent review. The maintainer's independent delivery review
is still required. I reopened the node and Lean signature and checked each row above.
The reduced closure uses exactly closed immersion, reducedness and image closure;
Tag 01J3 justifies this representation. The generic-point hypotheses use field-stalk
isomorphisms, not merely a map with generic image, which could miss a nontrivial
function-field extension. The two Cartesian squares retain the precise structure maps
and the identity on Spec L in the conclusion. I checked the projection equations yield
compatibility of the function-field identification with K, rather than just an abstract
field isomorphism. The final equation uses the M projection, and dense-open finiteness
uses the composite to S, rather than the map to N. No hypothesis or conclusion was
changed on this pass. No additional postponed declaration, definition node, dependency
repair, or statement correction is present.
