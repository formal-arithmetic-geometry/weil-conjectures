## Worker report

The delivery states `AlgebraicGeometry.exists_quasiSplitTower_smooth_resolution` in
`Sheaf.AlgebraicGeometry.QuasiSplitTowerSmoothResolution`. Its only theorem has the whole
proof `by sorry`; no definition or additional node is needed. The item's non-Lean fields are
unchanged. Source read directly: ILO, Travaux de Gabber, X Lemma 2.2 proof, printed
pp.149--150 (PDF pages 155--156). The paragraph beginning “successively applying” gives the
compatible modifications; its relative smooth-pair refinement and last sentence give the
relative SNC boundary and Cartier sub-divisor. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read, with `literature/blueprint/COMMITS.txt`; the item is a tool on its route, not the
unit's own statement. No statement correction or disputed assertion was required.

Hypothesis and clause mapping:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Field F; finite group J acting on F by field automorphisms | `F : Type u`, `[Field F]`, `J : Type v`, `[Group J] [Finite J]`, `γ : J →* (F ≃+* F)`; the group universe is independent. |
| Length d ≥ 0, tower T_d → … → T_0 = Spec F | `d : ℕ`, `T : Fin (d + 1) → Scheme.{u}`, `f : ∀ i : Fin d, T i.succ ⟶ T i.castSucc`; the specified identification `e₀ : T 0 ≅ Spec (.of F)` and `hq₀ : q 0 = e₀.hom` express the base stage up to its named canonical identification. |
| Integral schemes, finite type over F | `[hIntegral : ∀ i, IsIntegral (T i)]`; `q` are the structure maps; `[hft : ∀ i, LocallyOfFiniteType (q i)] [hqc : ∀ i, QuasiCompact (q i)]`. |
| Tower over F, compatible semilinear J-actions | `hq`, `τ : ∀ i, J →* Aut (T i)`, `hsemilinear`, `hequivariant`. The scalar map is `Spec.map (CommRingCat.ofHom (γ g⁻¹).toRingHom)`: the inverse is required by contravariance of Spec for left actions, as in the already landed plurinodal-field-alteration theorem. No faithfulness assumption is made. |
| Each f_i projective, flat, finitely presented | `hprojective : ∀ i, IsProjectiveBundle (f i)`, `hflat`, `[hfp : ∀ i, LocallyOfFinitePresentation (f i)]`. Projectivity implies quasi-compactness and quasi-separatedness, so local finite presentation here is exactly finite presentation, not a weakened hypothesis. |
| Nonempty connected reduced one-dimensional nodal geometric fibres | `hnodal : ∀ i, HasNodalGeometricFibres (f i)` includes connectedness, nonemptiness, dimension 1 and the completed local nodal equations; `hreduced : ∀ i, GeometricallyReduced (f i)` supplies reducedness of geometric fibres. |
| Smooth geometrically integral generic fibre | `hgeneric` applies `Smooth` and `GeometricallyIntegral` to `(f i).fiberToSpecResidueField (genericPoint (T i.castSucc))`. Integrality provides the unique generic point. |
| Quasi-splitness, rational singular point and both normalization branches | `hquasiSplit : ∀ i, HasQuasiSplitNodalFibres (f i)`, using the recorded predicate, not a private copy. |
| Finite disjoint sections in the relative smooth locus | `m : Fin d → ℕ`, `s i : Fin (m i) → ...`, `hsections` gives `s i j ≫ f i = 𝟙 _`; `hdisjoint` gives pairwise disjoint ranges; `hsmooth` puts them in `(f i).smoothLocus`. |
| J-stable union of markings M_i | `hmarkings` is equality of the union of ranges with its image under every `τ i.succ g`. Individual sections need not be fixed. |
| Z_0 empty, Z_i = f_i⁻¹ Z_(i−1) ∪ |M_i| | `Z : ∀ i, Closeds (T i)`, `hZ₀`, `hZ` specify exactly these closed subsets and their recursion. No extra Z is allowed by these equalities. Closedness follows from the projective separated maps and finitely many sections, so packaging the subsets as `Closeds` adds no geometric restriction. |
| f_i smooth over the complement of the preceding boundary | `hsmoothOff` uses the actual `morphismRestrict` of `f i` to the open complement of `Z i.castSucc`. |
| No condition on point stabilizers, fibre graphs, branches, sections | There are no such binders. `τ`, `ρ` are arbitrary finite-group actions satisfying only the displayed equivariance identities. |
| Integral smooth projective F-schemes S_i | Existential `S`, `p`, `(_ : ∀ i, IsIntegral (S i))` and `(∀ i, Smooth (p i) ∧ IsHProjective (p i) ∧ IsRegularScheme (S i))`. The source convention for projective over F is the dependency's `IsHProjective`. |
| S_0 = T_0; modifications identities for d=0 | `h₀ : S 0 = T 0`, `r 0 = eqToHom h₀`; together with `hq₀` and `r i ≫ q i = p i` this also fixes the zeroth structure morphism. When d=0 this is the only modification. |
| Semilinear J-actions on S_i | `ρ : ∀ i, J →* Aut (S i)` and the identity `(ρ i a).hom ≫ p i = p i ≫ Spec.map ... (γ a⁻¹)`. The monoid homomorphism contains the complete group law. |
| Equivariant projective birational surjections r_i | Existential `r`; `(ρ i a).hom ≫ r i = r i ≫ (τ i a).hom`; `IsHProjective (r i) ∧ Surjective (r i)`. Birationality is explicitly both a compatible isomorphism `e` between dense opens `U`, `V`, and bijectivity of the actual generic stalk map transported along `hη`. This is the canonical isomorphism on function fields, not an arbitrary abstract field equivalence. |
| Equivariant S_i → S_(i−1), commuting squares | Existential `g`; its equivariance identity and `g i ≫ r i.castSucc = r i.succ ≫ f i`. Its compatibility with the F-structure maps follows from this square and `r i ≫ q i = p i`. |
| E_i is the reduced inverse image of Z_i and relative strict SNC | `E i = ((Scheme.IdealSheafData.vanishingIdeal (Z i)).comap (r i)).radical` and `(E i).IsSmoothStrictNormalCrossingsDivisor (p i)`. This uses canonical ideal pullback and radical. |
| Every local ring regular | Existential `(_ : ∀ i, IsRegular (S i))` provides the stalkwise regularity instances used to type parameter systems; the conclusion also explicitly uses the recorded `IsRegularScheme` notion, including local Noetherianity. |
| Components through a point have equations distinct members of a regular parameter system | `C i : Fin (n i) → ...` has integral components, pairwise noncontainment, and union `E i = ⨅ j, C i j`, so it is exactly the reduced irreducible-component list. At each `x`, a list `t` satisfies `IsLocalRing.IsRegularSystemOfParameters t`. `K` indexes exactly components through x, and injective `κ : K → Fin t.length` assigns distinct parameters. The ideal of each component on an affine neighborhood, mapped by the actual germ to the stalk, equals `Ideal.span {t.get (κ j)}`. |
| Moreover arbitrary integral X with J-action, invariant effective Cartier C, dominant equivariant a : T_d → X, inverse image supported in Z_d | Universal final clause `∀ (X : Scheme.{u}) [IsIntegral X] (α : J →* Aut X) (D : X.IdealSheafData) (hD : D.IsInvertible) ... (a : T (Fin.last d) ⟶ X) [IsDominant a]`; `hDstable` is equality of pulled-back ideals, followed by equivariance of a and the stated containment as implications. Here `D` renders the input Cartier divisor C, reserving `C i` for boundary components. |
| Reduced Cartier pullback is effective Cartier | `(D.comap (r (Fin.last d) ≫ a)).radical.IsInvertible`. The category composite is r followed by a, exactly a r_d. |
| It consists of a subset of E_d components | `∃ K : Finset (Fin (n (Fin.last d))), ...radical = ⨅ j ∈ K, C (Fin.last d) j`. It is an equality of ideal sheaves, giving the actual reduced scheme structure, not just support containment. |
| It is relative strict SNC over F | The final `.IsSmoothStrictNormalCrossingsDivisor (p (Fin.last d))` of the same radical ideal. |
| Empty markings and empty Cartier divisor | No positivity requirement on m or n; `Fin 0` is allowed. For `D = ⊤` the support is empty, its pullback/radical is ⊤, and the empty K gives the empty component union (empty ideal infimum = ⊤). |

Dependency declarations read and used (module, name):

- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.
- `def-nagata-effective-cartier-ideal`: `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`, `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral` (also `AlgebraicGeometry.GeometricallyIrreducible`, `AlgebraicGeometry.GeometricallyReduced`).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth` (also `AlgebraicGeometry.SmoothOfRelativeDimension`, `AlgebraicGeometry.Etale`).
- `def-sfb-quasi-split-nodal-fibres`: `Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres`, `AlgebraicGeometry.HasQuasiSplitNodalFibres`.
- `def-trf-nodal-geometric-fibres`: `Sheaf.AlgebraicGeometry.NodalGeometricFibres`, `AlgebraicGeometry.HasNodalGeometricFibres`.
- `def-trf-projective-bundle-morphism`: `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`, `AlgebraicGeometry.IsProjectiveBundle`.
- `def-trf-smooth-strict-normal-crossings-divisor`: `Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor`, `AlgebraicGeometry.Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor`.
- `def-weil-field`: Mathlib `Field` (field binder).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType` (also `AlgebraicGeometry.QuasiCompact`).
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-weil-pbc-regular-system-of-parameters`: `WeilConjectures.RingTheory.IsRegularSystemOfParameters`, `IsLocalRing.IsRegularSystemOfParameters`.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `AlgebraicGeometry.Surjective`.

All recorded defining signatures and docstrings were opened. The withdrawn example
`lean/Sheaf/CategoryTheory/CompactObject.lean` has no declarations, so its node's current
upstream module `WeilConjectures.CategoryTheory.CompactObject` was read as the example.
The projective convention is the upstream `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`;
there is no duplicate definition. Finite type uses the recorded locally-finite-type plus
quasi-compact conjunction. `Scheme.functionField`, `Scheme.IdealSheafData.comap`, `.radical`,
`.vanishingIdeal`, and the scheme stalk/germ API are existing Mathlib constructions.
The extra public imports supply these constructions and actions/restrictions.

Already stated proof dependency modules are imported privately (except dependencies already
publicly imported for the statement). The source module for smooth-over-field regularity is
already exposed through `IsRegularScheme`. Unstated proof dependencies, hence no available
module import, are `lem-sc-integral-scheme-stalks-in-function-field`,
`lem-sfb-equivariant-log-smooth-fan-regularization`,
`lem-sfb-marked-nodal-relative-log-charts`, `lem-sfb-nodal-birational-base-change-geometry`,
and `lem-sfb-relative-nc-maximal-branch-strictification`. These are proof prerequisites,
not missing notions needed to state this item. The complete nine-step natural-language
proof and its cited uses are in the theorem docstring.

Edge cases checked by reading the quantified signature: d=0 has no transition maps,
sections or nontrivial modifications; r_0 is the transported identity. In particular its
boundary is empty. With d>0 and all markings empty, the recursion still permits Z_i empty
and every fibre condition is retained. At a point outside E_i, K is empty and the component
parameter clause is vacuous while the full parameter system remains. At a generic point
the parameter list can be empty. A zero-dimensional local ring permits the empty list.
The empty Cartier divisor selects no boundary components. Intersections of no boundary
components in the recorded relative SNC predicate recover S_i. No perfection, algebraic
closedness, characteristic, faithful action or stabilizer restriction was imposed on F/J.
Schemes/fields lie in one scheme universe u, as in the existing geometric-fibre API;
the finite acting group may lie in any universe v. An X in the final clause need not be
finite type, separated, proper, or an F-scheme. Its dominant map is not strengthened.

Searches made before writing:

- `msearch.py ... leanfinder "A finite equivariant quasi-split marked tower of nodal curves over a field admits a compatible smooth projective resolution with strict normal crossings boundary"`: eight hits, basic smoothness/standard-smooth-presentation definitions and lemmas only; none states the tower resolution.
- `msearch.py ... leansearch "Equivariant resolution of a marked nodal tower over a field with smooth strict normal crossings boundary"`: eight hits concerning étale schemes, residue-field scalar towers, and normalization; none states the result.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsHProjective"`: no hits, because the project-specific IsHProjective name is unknown to the public search index. The actual project source was then inspected directly.
- `msearch.py ... grep "quasi.?split|plurinodal|nodal.*resolution"`: zero Mathlib hits.
- `rg -n "lem-sfb-quasi-split-tower-smooth-resolution" lean/WeilConjectures` and `rg -n "quasi.split|plurinodal|nodal.*tower" lean/WeilConjectures`: no corresponding upstream theorem.
- `rg` of `lean/Sheaf/AlgebraicGeometry` for semilinear actions, birationality and tower notions found `EquivariantMarkedPlurinodalFieldAlteration.lean`, which constructs the input tower but does not resolve it, and birational generic-stalk-map examples. Read both that module's signature and `IntegralBirationalNormalIsomorphism.lean` for compatible canonical encodings. The former's private proof imports were not exposed as statement dependencies.
- `rg` of `lean/Sheaf`, `lean/WeilConjectures`, `dag/lean_names_upstream.json` for `quasi.split.*tower|tower.*smooth.*resolution|exists_quasiSplitTower`: only the input tower's proof text matched; no existing declaration.
- `python3 tools/blueprint_refs.py search quasi-split`: zero blueprint nodes match. No new notion/node is required; each notion is already in the statement dependencies or Mathlib.

Validation: `scompile.py NQ lem-sfb-quasi-split-tower-smooth-resolution <module>` compiled
both sandbox and exact library module modes on the server, 5.5 s and 5.1 s respectively,
with no reported errors or warnings. `set_option autoImplicit false` is explicit;
no diagnostics remain in the file and every line has at most 100 characters.

## Second reading by NQ

The dispatcher explicitly prohibited starting other agents. This section records a second
pass by the same worker, with the complete source node and generated Lean signature open;
it does not claim an independent reviewer. The maintainer's independent review reads the
delivery as required by the assignment.

On that second pass I checked the table above against every sentence in the node and the
actual signature. The field action uses inverse scalar automorphisms consistently with the
left scheme action. The zeroth scheme equality and transported identity fix the d=0 case;
merely giving an isomorphism at the resolution stage would not have recorded that clause.
Both senses of birationality are explicit, with the function-field comparison induced by r.
The finite component family is genuine: integral reduced component subschemes, no containment
between distinct supports, and ideal-sheaf union equal to E. Its local injection into t
specifies distinct parameters for individual components; it does not merely give a product
equation for E. The final sub-boundary equality uses exactly that same component family and
the actual radical pullback. No replacement by an arbitrary divisor/map or abstract field
isomorphism occurs. I also checked that smoothness off Z refers to the target-open restriction,
that markings may be permuted, and that no graph/branch/stabilizer condition was inserted.
No mismatch or node fault was found; no statement change, new node or dependency repair
was needed. The proposition occurrences `IsRegular`/`IsRegularScheme` are the same regularity
conclusion with typeclass plumbing, not additional geometric conditions. The only pending
proof is the named theorem above, with the complete node proof in its docstring.
