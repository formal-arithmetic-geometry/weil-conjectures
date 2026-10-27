## Worker report

The module `Sheaf.AlgebraicGeometry.RegularComponentEtaleStalkPrimes` states
`AlgebraicGeometry.regular_component_etale_stalk_primes`, with one `sorry` and no
definitions or proved lemmas. The natural-language statement is unchanged.
The node gains only its `lean` record and the already landed statement dependency
`def-trf-marked-ideal-order`: its `AlgebraicGeometry.HilbertSamuel.stalkIdeal` is
the existing construction of the stalk ideal of a quasi-coherent ideal sheaf.
This avoids a second definition, including at points outside a closed subscheme.

Hypotheses and clauses, matched individually:

| Node | Lean |
| --- | --- |
| Locally Noetherian scheme X | `{X D : Scheme.{u}} [IsLocallyNoetherian X]` |
| Reduced closed subscheme D of X | `d : D ⟶ X`, `[IsClosedImmersion d]`, `[IsReduced D]` |
| Finite index set F | `{F : Type v} [Finite F]`; the index universe is unrestricted |
| Reduced closed components of D | `C : F → Scheme.{u}`, `k : (a : F) → C a ⟶ D`, closed immersion and reducedness instances for every a |
| Exactly all components | `hcomponents : Set.range (fun a ↦ Set.range (k a)) = irreducibleComponents D` |
| Distinct components | `hdistinct : Function.Injective (fun a ↦ Set.range (k a))` |
| Every component regular | `hregular : ∀ a, IsRegularScheme (C a)` |
| Étale v:W→X and w in W | `f : W ⟶ X`, `[Etale f]`, `w : W`; f is the node's v |
| x, A, R, canonical stalk map | Direct expressions `f w`, `X.presheaf.stalk (f w)`, `W.presheaf.stalk w`, `(f.stalkMap w).hom`; no extra choices or hypotheses |
| I the stalk ideal of D | `I`, `hI : I = HilbertSamuel.stalkIdeal d.ker (f w)` |
| Components through x | `Fx : Set F`, `hFx : Fx = {a | f w ∈ Set.range (k a ≫ d)}` |
| Component ideals p_a | `p : F → Ideal ...`, `hp : ∀ a, p a = HilbertSamuel.stalkIdeal (k a ≫ d).ker (f w)` |
| Extended ideals q_a | `q`, `hq : ∀ a, q a = (p a).map (f.stalkMap w).hom` |
| Exactly the distinct minimal primes over I | `Set.BijOn p Fx I.minimalPrimes`; this includes both directions and injectivity |
| O_(D_a,x)=A/p_a | For a in Fx and each point z mapping to x, an equivalence `(A ⧸ p a) ≃+* (C a).presheaf.stalk z` commuting with the quotient map and the actual structural stalk map; `stalkCongr` transports x along hz |
| Closed pullback is Spec(R/q_a) | For a in Fx, an isomorphism from `pullback (k a ≫ d) (W.fromSpecStalk w ≫ f)` to the quotient spectrum, commuting with its map to Spec R |
| Nonzero regular local domain | `Nontrivial`, `IsRegularLocalRing`, and `IsDomain` of the same quotient ring |
| q_a proper prime | `(q a).IsPrime ∧ q a ≠ ⊤` |
| Contraction equals p_a | `(q a).comap (f.stalkMap w).hom = p a` |
| Distinct q_a | `Set.InjOn q Fx` |
| V(IR) is the union of V(q_a) | Equality of `PrimeSpectrum.zeroLocus` of the mapped I and the double union `⋃ a ∈ Fx, ...` |
| Missing components have empty pullback | `∀ a ∉ Fx, IsEmpty (pullback ... : Scheme.{u})` |

The families p and q are defined on F so their formulas also make sense outside Fx;
their values are completely determined by hp and hq. No primality, regularity or
nonzero-quotient assertion is imposed outside Fx. The quotient equivalence is
quantified over every z over x; Fx and the closed embeddings guarantee such a z
exists and is unique. This is the component stalk at x, not an arbitrary ring
isomorphism. The pullback isomorphism is also over Spec R.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  which is `IsLocallyNoetherian X ∧ IsRegular X`; its upstream stalk class is
  `AlgebraicGeometry.IsRegular` in `WeilConjectures.AlgebraicGeometry.Regular`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, using Mathlib's stalk carrier. Here only
  the ring-stalk specialization is needed, with `Scheme.Hom.stalkMap`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.MarkedIdealOrder`:
  `AlgebraicGeometry.HilbertSamuel.stalkIdeal`; its full definition takes the
  supremum of the affine ideals extended along their germ maps. This is why the
  landed node `def-trf-marked-ideal-order` was added to stmt_deps.

Proof imports are plain imports, retaining the recorded proof plan:
`TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding`,
`finiteIntersection_etale_stalk_model`, the étale base-change instances,
`IsRegularLocalRing.isDomain`,
`Module.FaithfullyFlat.tensorProduct_mk_injective`, and
`Scheme.finite_affine_tensor_base_change`. The two proof nodes
`lem-sfb-closed-component-stalk-calculus` and `lem-sfb-etale-stalk-invariants`
have no Lean or Mathlib declaration in this checkout; they are not needed to type
the present statement and have no module to import. Their exact role remains in
the proof docstring. No dependency module or extra theorem was introduced.

Sources read: local Stacks `algebra.tex`, regular-goes-up (07NF), regular-domain
(00NP); `more-algebra.tex`, regular-etale-extension (0AH0); `schemes.tex`,
fibre-product-affine-schemes (01I4) and reduced-closed-subscheme (01J3).
The inherited stage-1 proof is transcribed in six steps in the declaration
 docstring, including the local affine reduction, contraction using faithful
flatness, the finite prime-product argument, and the missing-component case.

Edge cases checked before finalizing:

- Empty F forces D empty by the component enumeration. I is the unit ideal;
  Fx and the minimal-prime set are empty. The closed-set equality remains empty.
- x outside D allows nonempty F but empty Fx. All pullbacks of components are
  empty; no nontrivial quotient claim is made for them.
- Empty W or X has no w; the universal assertion requires no artificial point.
- D=X with X regular and integral has the one component ideal zero. Its étale
  stalk quotient is the stalk R itself, a regular local domain.
- Two regular branches meeting (e.g. V(st) in the affine plane) yield the two
  different minimal primes; contraction prevents their merging in the étale
  stalk. The ambient X need not be regular.
- A globally disconnected étale pullback is allowed: only its local ring at w
  is asserted to be a domain. No global integrality is asserted.
- Arbitrary characteristic and arbitrary index universe v are retained.

Searches made with the prescribed msearch wrapper:

- LeanFinder: `Minimal primes of reduced closed subscheme at a point extend to
  distinct prime ideals in an etale stalk when all components are regular`.
  Eight results, headed by `Algebra.etaleLocus`, `Algebra.mem_etaleLocus_iff`,
  `Algebra.IsEtaleAt`; none states the component-family theorem.
- Loogle: `"IsEtale", "IsRegularLocalRing"`: zero results.
- Mathlib grep: `IsEtale.*IsRegular|IsRegular.*IsEtale|component.*stalk`, restricted
  to AlgebraicGeometry: two ingredient hits, Properties and Geometrically/Reduced;
  no exact statement.
- LeanSearch: `Ideals of regular irreducible components extend to distinct prime
  ideals in an etale stalk and contract to their original minimal primes`.
  Eight results: `Ideal.minimalPrimes`,
  `PrimeSpectrum.vanishingIdeal_irreducibleComponents`, primes-over and
  localization results. These supply ingredients only.
- `rg` in `lean/WeilConjectures` for the blueprint id and candidate declaration
  name: no match; searches for regular/component and stalk/ideal identify only
  ingredients. `rg` in `lean/Sheaf` identifies the existing stalk-ideal construction
  in MarkedIdealOrder and nearby boundary definitions, no exact theorem.
- Candidate full theorem name also checked in Mathlib and
  `dag/lean_names_upstream.json`: no collision.

Validation: prescribed `scompile.py` compiled both its sandbox and final library
module forms cleanly (8.4 s and 6.1 s), with no diagnostics. Every variable and
universe is explicitly bound; the file has `autoImplicit false`. Every line is
at most 100 characters. There is one named theorem, proof `sorry`, and no data
construction with postponed content. No statement fault or disputed claim found.

## Second reading by Q31

This is an in-session second pass; the worker brief forbids starting another
agent and assigns the independent review to the maintainer. With the node and
complete file open, I checked every row of the correspondence above, especially
that minimal-prime enumeration is bijective rather than merely surjective, that
regularity belongs to the component schemes rather than X, that contraction is
along the actual étale stalk map, and that quotient equivalences and pullback
isomorphisms respect their structural maps. The two empty cases remain in scope.
No mismatch was found and no natural-language statement correction was made.
The only additional statement dependency is the already landed stalk-ideal
construction; it introduces no mathematical hypothesis.
