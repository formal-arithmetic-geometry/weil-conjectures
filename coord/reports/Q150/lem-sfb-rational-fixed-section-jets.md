## Worker report

The delivery states `AlgebraicGeometry.RationalFixedSectionJets.rational_fixed_section_jets`
in `Sheaf.AlgebraicGeometry.RationalFixedSectionJets`. Its only postponed proof is this
named theorem. All eight auxiliary constructions have real data and belong to the local
quotient, section, and scalar-extension construction explicitly described in this node.
There are no new nodes, dependency replacements, or statement corrections.

Source read: Milne, Algebraic Groups (2017), Proposition 8.9, printed p.150 (the paragraph
constructing the natural representations on the local quotients), and Proposition 8.25,
printed p.154 (the rational-action setting). The node's eight detailed proof steps supply
the continuation from a partial fixed section to actions on all finite neighbourhoods;
all eight appear in the theorem docstring. This statement does not use the faithfulness
argument or the stabilization assertion later in the proof of Proposition 8.9.

The source ring in `JetRing X x n` is exactly `X.left.presheaf.stalk x`. Its scalar map is
`k -> Γ(X,O_X) -> O_(X,x)`, with the first arrow induced by the structure morphism and the
second the germ. `stalkAlgebra` constructs that composite. `JetRing X x n` is the quotient
by the ordinary ideal power `maximalIdeal (...) ^ (n+2)`. Thus Lean index n corresponds
to the paper's index n+1, bijectively covering precisely all indices at least one. At a
k-rational point, the kernel of the point's local map to k is the maximal ideal: that map
is local and its residue-field map is an isomorphism, since it is split by the scalar
map. Using `IsLocalRing.maximalIdeal` therefore uses the same ideal as the node.

Hypothesis-by-hypothesis rendering:

| Node hypothesis | Lean |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k]`, declared in the section, and `[IsAlgClosed k]` on the theorem |
| k-group scheme G | `G : Over (Spec (.of k))` and `[GrpObj G]` |
| Smooth, connected, separated G | `[Smooth G.hom] [ConnectedSpace G.left] [IsSeparated G.hom]` |
| Finite type G | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| Integral separated finite-type k-scheme X | `X : Over (Spec (.of k))`, `[IsIntegral X.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` |
| Nonempty dense open subscheme Y of X | `Y : Over ...`, `j : Y ⟶ X`, `[IsOpenImmersion j.left] [Nonempty Y.left]`, and `hY : DenseRange j.left` |
| Regular action a on Y, unit and multiplication identities | `[ModObj G Y]`; the morphism is `γ[G,Y]` and the two identities are the fields of `ModObj` |
| Fibre products over k | The Cartesian monoidal tensor in `Over (Spec k)`; e.g. `G ⊗ X` is the scheme fibre product |
| Rational extension alpha, with largest domain D | `f : (G ⊗ X).left.PartialMap X.left` and `hmax : f.domain = f.toRationalMap.domain`; `f.toRationalMap` is alpha, `f.domain` is D, `f.hom` its morphism on D |
| Extension of the given action on G times Y | `hrestrict` gives its factorization `dY` into D and the equations `dY ≫ D.ι = (G ◁ j).left` and `dY ≫ f.hom = (γ[G,Y] ≫ j).left` |
| Rational point P | `P : 𝟙_ (Over (Spec (.of k))) ⟶ X`; its underlying point is `P.left (IsLocalRing.closedPoint k)` |
| (e,P) belongs to D | `he`, applied to the unit section `η[G]` and `sectionMap G X P` |
| alpha is constant P along the open V of the section | `hfix`: for every test scheme T and every pair of maps g:T→G and d:T→D with the same section composite, `d ≫ f.hom = g ≫ (toUnit G ≫ P).left` |

The maximal partial representative presentation does not choose an arbitrary smaller
domain: `hmax` equates its domain with Mathlib's union of all representative domains.
It is equivalent to specifying alpha with its maximal representative. The extension
condition `hrestrict` expresses the given regular action as its restriction. Such a
factorization is inherent in a maximal representative of the rational extension: the
original action is a representative, and equality on overlaps follows from the
scheme-theoretic density of G times Y and separatedness of X. It adds no extension
across the boundary of Y. There is no assumption of a global regular action on X.

The test-scheme formulation of `hfix` is equality of morphisms on the pullback of D
along `g ↦ (g,P)`. This pullback is precisely the open V in G. Taking T=V and its
canonical two morphisms recovers the node's restriction equality. Conversely that
restriction equality implies every instance of `hfix`. This tests the full scheme
structure, including nonreduced test schemes.

Conclusion-by-conclusion rendering:

| Node conclusion | Lean |
| --- | --- |
| D contains the whole section G times P | The first existential `d : G.left ⟶ f.domain.toScheme` and `d ≫ f.domain.ι = (sectionMap G X P).left` |
| Its restriction is constant P as a morphism | `d ≫ f.hom = (toUnit G ≫ P).left` |
| Actual quotients Q_n are nonzero finite-dimensional k-vector spaces | `Nontrivial (JetRing ... n)` and `FiniteDimensional k (JetRing ... n)` in the first indexed conjunction |
| A choice of basis for GL(Q_n), with positive dimension | `c : ℕ → ℕ`, `b n : Module.Basis (LinearGroupSchemes.Index (c n)) k (JetRing ... n)`, and `0 < c n` |
| X_n = Spec Q_n | `jetScheme X x n` is that affine scheme over k |
| Canonical i_n : X_n → X is a closed immersion | `i n` is a k-morphism with `(i n).left = jetInclusion X x n`, followed by `IsClosedImmersion (i n).left`; `jetInclusion` is Spec of the quotient map followed by `X.fromSpecStalk x` |
| G times X_n lies in D | The indexed existential `dn`, with `dn ≫ D.ι = (G ◁ i n).left` |
| Restriction factors through i_n and gives an action | `a n : ModObj G (jetScheme ... n)` and `dn ≫ f.hom = ((a n).smul ≫ i n).left`; `ModObj` carries the action laws |
| Group-scheme homomorphism rho_n to GL(Q_n) | `ρ n : Grp.mk G ⟶ Grp.mk (GeneralLinearGroup (Index (c n)) k)`; its underlying k-morphism is `(ρ n).hom.hom`, whose `IsMonHom` instance is supplied by the bundled morphism |
| rho_n(B)(g) is a B-algebra automorphism of B tensor Q_n | `r n B g : (B ⊗[k] JetRing ... n) ≃ₐ[B] (B ⊗[k] JetRing ... n)` |
| This is the same rho_n, in the chosen basis | The matrix of `(r n B g).toLinearMap` in `(b n).baseChange B` equals `GeneralLinearGroup.homMulEquiv ... (g ≫ (ρ n).hom.hom)` |
| The representation is inverse pullback of the action | The displayed Spec equation says `Spec(r n B g) ≫ tensorJet = (lift (tensorBase ≫ g⁻¹) tensorJet ≫ (a n).smul).left` |
| The quotient maps intertwine the representations | The indexed equality with `Algebra.TensorProduct.map (AlgHom.id k B) (jetTransition ... n)` commutes with `r (n+1) B g` and `r n B g` on every z |
| K_n is the scheme-theoretic kernel | `GrpObj.ker (ρ n).hom.hom`, which is the chosen pullback along the target unit section, with inclusion `GrpObj.kerι ...` |
| Kernels are closed finite-type subgroup schemes | `IsClosedSubgroupScheme (GrpObj.kerι ...)`, `LocallyOfFiniteType (GrpObj.ker ...).hom`, and `QuasiCompact (GrpObj.ker ...).hom` |
| K_(n+1) is contained in K_n scheme-theoretically | The final existential t between the two kernel objects, `IsClosedImmersion t.left`, and its equation over G |

`r` is not an extra assumption: it is existential output, identified with rho_n on every
commutative test algebra and with the inverse-pullback action by the Spec equation.
These identifications also force its naturality and the representation law. Inverting g
in that equation is necessary: pullback of the original left action alone reverses
composition. No uncharacterized comparison map or chosen representation is an input.

Dependency declarations read and used (the Mathlib matches are used directly when the
node has no lean record):

| Node | Module and declaration |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`, `Field` |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`, the algebraically closed-field clause of its recorded match |
| def-sc-group-scheme | `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`, `CategoryTheory.Grp`; homomorphisms use `IsMonHom` through `Grp` morphisms |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth` |
| def-weil-connected-scheme | `Mathlib.Topology.Connected.Basic`, `ConnectedSpace` (includes nonemptiness) |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`, and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `IsSeparated`, as recorded by the proper-morphism node; it is the closed-diagonal property |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral` |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`; the Cartesian tensor of Over is this construction |
| def-weil-open-immersion | `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion` |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`, `Scheme`, `Scheme.Hom` |
| def-weil-pbc-algebra-hom-quotient | `Mathlib.Algebra.Algebra.Hom`, `AlgHom`; `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Ideal.Quotient.algebra`, `Ideal.Quotient.mk`, `Ideal.Quotient.factorₐ`; ordinary ideal powers from Mathlib |
| def-weil-finite-dimensional-subspace | `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, `FiniteDimensional` |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion` |
| def-sc-general-linear-group | `Sheaf.AlgebraicGeometry.LinearGroupSchemes`, `LinearGroupSchemes.Index`, and its reused upstream `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`, `GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv` |
| def-weil-pbc-module-tensor-product | `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct`; `Algebra.TensorProduct.map`, `includeLeft`, and `includeRight` provide the corresponding algebra maps |
| def-sc-group-scheme-subgroup | `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, `IsClosedSubgroupScheme` |

The relevant recorded proof-dependency modules are imported with plain imports, unless
already public statement imports: upstream Regular (`IsRegular.of_smooth`,
`IsRegular.isIntegral`), DensePoints (`Scheme.Hom.denseRange_fieldPoints`), the upstream
Separated extension (`ext_of_isSchemeTheoreticallyDominant_of_isSeparated`),
ClosedPointField (`closedPoint_iff_residueField_trdeg_zero_and_finite`), IdealSheaf.Basic
(`Hom.ker`, powers, `Hom.le_ker_comp`), GammaSpecAdjunction
(`ΓSpec.locallyRingedSpaceAdjunction`), Yoneda (`Yoneda.fullyFaithful`), the Cartesian Grp
kernel module (`GrpObj.ker`, `kerι`), and ClosedImmersion (`lift`, `lift_fac`,
`of_comp_isClosedImmersion`). The base-change/thickenings proof node has no recorded
Lean declaration on the read base, so there is no module to import for it. It is only a
proof dependency; this theorem's statement uses the real explicit local quotients and
therefore needs no assumed version of that theorem.

Searches (2026-10-24; wrapper results are also in sandbox searches.jsonl):

- LeanFinder: “A rational algebraic group action fixing a rational point induces compatible
  algebraic representations on its local ring quotients by powers of the maximal ideal”.
  Eight hits: invariant-quotient stabilizer homomorphisms and residue-field actions; none
  constructs the rational fixed-section jets.
- Loogle: `"AlgebraicGeometry.Scheme.RationalMap"`. Twelve hits, including `RationalMap`,
  `domain`, `toPartialMap`, `representative`, `IsOver`, and conversion lemmas. Reused the
  actual `PartialMap` quotient and its domain; no private rational-map definition.
- Mathlib grep wrapper: `jet|rational.*action|fixed.*section`, under AlgebraicGeometry:
  zero hits.
- LeanSearch: “A rational group scheme action at a fixed point induces representations on
  powers of its maximal ideal”. Eight hits: `Representation.toInvariants`, abstract ideal
  actions, `IsLocalRing.ResidueField.residue_smul`, and related abstract-action results;
  none matches the theorem.
- `rg` in the project's Sheaf and WeilConjectures algebraic geometry sources for
  `rationalFixed|RationalAction|rational.*[Aa]ction|Jet|jet|pointThickening` found unrelated
  finite-jet smoothness and rational Tate-action modules, not this statement.
- Search for the exact node id in WeilConjectures returned no declaration.
- Further source searches located `CategoryTheory.ModObj` (reused), the upstream
  `GeneralLinearGroup` and `homMulEquiv` (reused), `Scheme.fromSpecStalk` (reused), the
  ideal quotient `factorₐ` (reused), and tensor-base-change bases (reused).
- Exact-name collision search for the new namespace, theorem, and JetRing found no existing
  declarations. Other `stalkAlgebra` names are in different namespaces and encode different
  bases or the generic affine/localization case.

Edge cases checked before writing and on the resulting statement:

- The first index is Q_1, not the zero quotient or an omitted first jet: n=0 means m^2.
- X=Spec k gives Q_n=k with dimension one and trivial representations; positive c is valid.
- Singular integral X is allowed; there is no smoothness, regularity, or normality assumption
  on X and no replacement by a completion.
- Positive characteristic is unrestricted, including infinitesimal and nonreduced kernels.
- G need not be affine. The only scheme-theoretic properties imposed are precisely the
  smooth, connected, separated, finite-type hypotheses in the node.
- The trivial group and a trivial action satisfy the statement; there is no faithfulness
  assumption or conclusion that the kernels become trivial.
- Empty Y is excluded exactly as in the node. ConnectedSpace excludes empty G, and
  IsIntegral excludes empty X.
- The test algebra B can be nonreduced or the zero algebra; no Nontrivial, finite type,
  reducedness, or field condition is placed on B. Scalar extension and the displayed
  algebra-automorphism equations still make sense in these cases.
- hfix is scheme-theoretic equality on V, not merely equality on k-points. The output
  factorization through D contains the entire section as a scheme.
- Kernels use the pullback definition, not their reduced subschemes or their k-points;
  the descending maps are closed immersions over G.
- All universes and variables are declared explicitly; `set_option autoImplicit false`
  enforces this. GL indices are ULift(Fin c), matching the upstream universe of k.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The example CompactObject
module is now a withdrawn empty module on this read base; the delivery follows the current
module-mode header rule and the extant LinearGroupSchemes module conventions instead.

## Second reading by Q150

Worker self-audit, after opening the completed module and the node together. This is not
claimed to be an independent agent review: the dispatcher explicitly starts a single worker,
forbids spawning other agents, and assigns independent review to the maintainer.

The audit checked every row of both rendering tables above against the actual signature.
The inverse in the Spec equation has the correct variance; the basis matrix is identified
with rho on every test algebra; the transition uses consecutive ideal powers; the final
map is from K_(n+1) to K_n and commutes with their inclusions. The input f has its maximal
domain, and hfix is a morphism equality after arbitrary scheme tests. No extra affine,
faithfulness, smoothness-of-X, characteristic, or reduced-test-algebra hypothesis occurs.
The canonical jet maps are constrained to be the quotient/stalk construction. No silent
statement correction was made. One compiler whitespace warning in γ[G,Y] was repaired.
The revised module compiled cleanly, in both server sandbox and library modes, with only
the expected sorry handling for the theorem. The delivery dry run is recorded below.

Validation: `deliver2.py Q150 lem-sfb-rational-fixed-section-jets --no-push` printed
`OK (dry run): commit 323185c8a18 passes the preflight and compiles; nothing pushed`.
The packet contains exactly the module, the item's lean-only node update, and this report.
