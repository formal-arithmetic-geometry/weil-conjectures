## Worker report

The module `Sheaf.RingTheory.EquivariantMarkedCylinderAlgebraization` states
`RingTheory.exists_equivariant_marked_cylinder_algebraization`, with one `sorry` proof.
It has no new definitions or axioms. The node statement and dependency lists are unchanged;
only its `lean` record is added. No correction or disputed statement is needed.

I read the node and all nine statement dependency records, the definitions and docstrings
in their recorded Mathlib sources, and the live source of
`WeilConjectures.RingTheory.QuasiFiniteAtPrime` through `scompile.py --source` (that source
is absent from the older checkout). I also read ILO, Expose V, printed pp. 63--68:
1.1.1--1.1.3, 1.2.4, 2.1.1--2.2.8, and 3.2.1--3.2.4. The last two pages explicitly descend
the finite invariant model and all primary markings by the indicated coordinate change.

The hypothesis and conclusion correspondence is as follows. Here `R` abbreviates, in this
report only, `MvPowerSeries (Fin (n + 1)) V`, and `D` abbreviates
`MvPowerSeries (Fin n) Λ`; there are no local notations or let binders in the signature.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| V is a field or complete DVR; its fixed ring is a field or complete DVR respectively | `[CommRing V] [IsDomain V] [IsLocalRing V]`, maximal-ideal `IsAdicComplete`, and `hkind`; the same local/completeness instances for the subring `Λ`, with `hΛ : Λ = FixedPoints.subring V H` |
| B is a complete Noetherian normal local domain | `[CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]` and maximal-ideal `IsAdicComplete` |
| r >= 1 | the ring has `Fin (n + 1)` variables, for arbitrary `n : ℕ` |
| Injective module-finite local map from the power-series ring | `[Algebra R B] [Module.Finite R B] [IsLocalHom (algebraMap R B)]` and `hinj` |
| Coefficient subring V in B inducing an isomorphism on residue fields | the composite `R → B` with `MvPowerSeries.C`; injectivity follows from `hinj` and injectivity of constants; `hres` gives a residue-field ring equivalence commuting with the coefficient inclusion and both quotient maps |
| Finite group H of invertible order, acting by local automorphisms | `[Group H] [Finite H]`, the two `MulSemiringAction` instances and `horder`; a group ring action gives automorphisms, and automorphisms of a local ring preserve its maximal ideal |
| Compatibility with the finite map and fixed variables | `hequiv`, using coefficientwise `MvPowerSeries.map (MulSemiringAction.toRingHom H V h)`; coefficientwise action fixes every formal variable |
| H is trivial in the field case | `Subsingleton H` in the field alternative of `hkind` |
| Some f nonzero modulo m_V, with etale map after inverting f | arbitrary `f`, `hred`, and `hetale` for the canonical `IsLocalization.Away.map`; quantifying over every such f is equivalent to the existential hypothesis formulation |
| A₀ = B^H | `A₀ : Subring B` and `hA₀ : A₀ = FixedPoints.subring B H` |
| Arbitrary finite family I₁,...,I_s | `s : ℕ`, `I : Fin s → Ideal A₀` |
| H-equivariant change of formal coordinates fixing V | `c : R ≃ₐ[V] R` and its displayed commutation equation with each coefficient action; its images of `MvPowerSeries.X i` are the coordinates u_i |
| Complete coefficient ring D = Λ[[u₁,...,u_{r-1}]] | `D = MvPowerSeries (Fin n) Λ`, mapped by coefficient inclusion, `rename Fin.castSucc`, then `c`, then `R → B` |
| Inclusion D → A₀ is exactly that defined by invariant coordinates | the existential `d` and `A₀.subtype.comp d = ...`; this is an equality of complete ring homomorphisms, not just values on polynomial generators |
| Finite-type D[T]-algebra C | `C : Type u`, `CommRing C`, `a : Polynomial D →+* C`, `hft : a.FiniteType` |
| Maximal n above (m_D,T) | `p : PrimeSpectrum C`, `p.asIdeal.IsMaximal` and `p.asIdeal.comap a = Ideal.comap Polynomial.constantCoeff (IsLocalRing.maximalIdeal D)`; the latter ideal is exactly (m_D,T) |
| Quasi-finite map: finite spectra of fibres and finite residue extensions | `Algebra.IsQuasiFiniteAtPrime (Polynomial D) C q` for every `q`, with the exact algebra instance `a.toAlgebra` and finite-type proof `hft`; for a finite-type map this is equivalent to the stated finite fibres and finite residue extensions |
| C/n finite over D/m_D | `k : (D ⧸ m_D) →+* (C ⧸ p.asIdeal)`, characterized by its quotient-map square, and `k.Finite`; quotient-map surjectivity makes k unique and canonical |
| Ideals J₁,...,J_s in C | `J : Fin s → Ideal C` |
| Isomorphism of the maximal-ideal completion of C_n with A₀ | `e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal) ≃+* A₀` |
| This is a D-algebra isomorphism | the equation `e (completionMap (localizationMap (a (Polynomial.C x)))) = d x` for every `x : D`; giving ring-equivalence linearity explicitly is equivalent to `≃ₐ[D]` for these structural maps |
| It carries every extended marking onto I_i | the final `Ideal.map` equality for every `i : Fin s`, with the composite C → C_n → completion → A₀ |
| s=0, and zero and unit ideals permitted | no nonemptiness or propriety hypothesis anywhere on s, I or J |

All mathematical data are explicit existing Mathlib constructions. `Λ` and `A₀` are
subrings with equality identifications, rather than arbitrary isomorphic rings. Completeness
of V is automatic in the field alternative and required in the DVR alternative. The local
structure on Λ is unique; its completeness is precisely the node's assumption on V^H.
The coefficient inclusion into B is derived from the given finite local power-series map,
so no extra inclusion is chosen. The residue-field equivalence in `hres` is tied to this inclusion by its quotient-map square,
so no independent coefficient map or extra local-map hypothesis is imposed.
An algebraic ring automorphism of the local power-series ring preserves its maximal ideal
and its powers, hence is automatically continuous for the formal adic topology.

Statement dependencies used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`,
  `IsAdicComplete`, `AdicCompletion`, its ring structure and canonical `algebraMap`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries`, `MvPowerSeries.C`, `.map`; `.Rename` supplies the smaller coordinate inclusion.
- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing` (the dependency is a Mathlib leaf without a lean record).
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`;
  `RingHom.Finite` is the same notion for the quotient-field homomorphism k.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`; here the ring-map form `RingHom.Etale` is used as authorized
  by brief-stage2 §3 (ETALE RING MAPS), for the specified localized finite ring map.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`, `RingHom.FiniteType`.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`; residues at maximal ideals are their canonical quotient fields.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`:
  `WeilConjectures.RingTheory.QuasiFiniteAtPrime`, `Algebra.IsQuasiFiniteAtPrime`.

The fixed subrings use `FixedPoints.subring` from
`Mathlib.Algebra.Algebra.Subalgebra.Operations`, not a new invariant-ring definition.
Normality uses Mathlib's `IsIntegrallyClosed` with `IsDomain`. All recorded proof-dependency
modules are imported, privately when only the proof needs them. Mathlib leaf proof modules
are imported too. The five genuine unstated proof prerequisites (trace-one finiteness,
finite-coefficient cylinder, primary dichotomy, vertical symbolic powers and pointed-etale
henselization limit) are described in the theorem docstring and remain DAG prerequisites;
they introduce no notion needed by this statement, so no duplicate theorem is declared.

Edge cases checked against both source and signature:

- `r = 1` is `n = 0`: the smaller variable set is empty, so D is canonically Λ;
  `rename Fin.castSucc` is still the coefficient inclusion, and the cylinder variable remains.
- `s = 0` is the empty type `Fin 0`: both markings have empty domain and the final universal
  condition is vacuous, while the algebra and completion conclusions remain present.
- Zero and unit markings are arbitrary ideals, with no primary/proper/nonzero restrictions.
  Their images under the completion equivalence give exactly zero and the unit ideal.
- The trivial group, including a field coefficient ring, is allowed; nonfaithful actions
  are also allowed, since neither the source nor the Lean assumes faithfulness.
- No characteristic, perfection, algebraic closedness or residue-finiteness assumption
  was added on V or B. The completion and all residue extensions use the specified ideals.
- V and B may be put in any common universe u, with an independent group universe v;
  the finite-type model can be taken in u (finite presentation over D[T]). No universal
  quantification over test algebras in a smaller independent universe occurs.

Searches (all before choosing the declaration, no exact existing theorem found):

- `msearch.py ... leanfinder "Marked invariant algebras descend to a polynomial cylinder"`:
  8 hits, polynomial formal smoothness, algebra generators and homotopical cylinders;
  none is the invariant marked-completion algebraization theorem.
- `msearch.py ... loogle "IsNoetherianRing, AdicCompletion, MvPowerSeries,
  IsDiscreteValuationRing, Module.Finite, AlgebraicGeometry.Etale, RingHom.FiniteType,
  Localization.AtPrime, IsQuasiFiniteAtPrime"`: no hits; IsQuasiFiniteAtPrime is
  project-specific. Its exact declaration was subsequently read from live source.
- `msearch.py ... grep "marked.*cylinder|equivariant.*algebraization|fixedSubring" RingTheory`:
  0 hits in Mathlib.
- `msearch.py ... leansearch "finite group invariant normal complete local ring
  algebraization ideals over power series polynomial ring"`: 8 hits, local power-series
  rings and Weierstrass quotients, no theorem giving the requested marked invariant model.
- `rg` for `equivariant.*cylinder|marked.*cylinder|MarkedCylinder|cylinder.*algebra|
  algebraization` in upstream `WeilConjectures` and project `lean/Sheaf`: related Elkik,
  formal glueing, conormal torsion and Weierstrass modules, no exact statement.
- `rg` and the requested id search in upstream `WeilConjectures`: no occurrence of the
  item id or this declaration. `tools/lean_names_upstream.py show <item>` gave no match.
- `tools/blueprint_refs.py search cylinder`: no blueprint node matching cylinder.
- Source searches for invariants found the existing `FixedPoints.subring` definition,
  so no helper invariant-ring definition or new node was introduced.

Validation: `scompile.py Q59 lem-per-equivariant-marked-cylinder-algebraization
lean/Sheaf/RingTheory/EquivariantMarkedCylinderAlgebraization.lean` compiled the module
in both sandbox and library positions. The final check is repeated by `deliver2.py`.

## Second reading by Q59

This is the author's final clause audit, not an independent agent review; the dispatched
workflow assigns independent review to the maintainer. I reopened the source statement,
node, and final signature, and checked the entire correspondence table above. I removed
an explicit coefficient-map `IsLocalHom` binder and expressed the residue-field isomorphism
by a ring equivalence with its quotient-map square: the compiler could not infer locality
of the coefficient composite, although it follows mathematically from the given local map.
I also added all available Mathlib proof imports. The canonical
coordinate inclusion is specified on all power series, not merely their variables. The
completion isomorphism is linear for exactly that inclusion, and the same isomorphism
transports every marking. The finite residue extension is tied to the actual quotient
square. No statement mismatch, unbound universe, new definition, missing marking, or
unrecorded statement correction was found.
