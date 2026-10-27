## Worker report

The module `Sheaf.Paper.P1CounitScalar` states
`AlgebraicGeometry.Etale.p1_counit_scalar`, with `sorry`. It states both the actual
normalized counit equation and the inverse-beta transpose characterization of the
canonical comparison. No definitions are introduced and no mathematical statement
is changed. Four already landed statement dependencies are added to record the
existing interfaces used to spell out the normalized data and comparison.

The blueprint source read is main-20261015,
`sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
the Charts paragraph, especially its scalar-extended counit and unique-transpose
sentences. The theorem docstring gives all six steps of the node's expanded proof.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Field k, characteristic p>0, prime ell different from p | `k : Type u`, `[Field k]`, `[CharP k p]`, `_hp : 0 < p`, `[Fact ell.Prime]`, `_hEll : p ≠ ell` |
| Finite commutative rings and unital map A→B | `{A B : Type (u+1)}`, `[CommRing A]`, `[CommRing B]`, `[Finite A]`, `[Finite B]`, `φ : A →+* B` |
| Common annihilator N=ell^n≥1 | `n : ℕ`, `hA : ((ell ^ n : ℕ) : A)=0`, `hB : ((ell ^ n : ℕ) : B)=0`; positivity follows from primality, including n=0 |
| Separated finite-type base S over k | `S : Scheme.{u}`, `[S.Over (Spec (.of k))]`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` of its structure map |
| P=P¹_S and q:P→S, with their inherited k-structures | The published `ProjectiveLine S` and `ProjectiveLine S ↘ S` throughout; no arbitrary scheme or morphism substitutes for them |
| Small ordinary-etale module derived categories and derived coefficient extension | `Etale.DerivedCategoryModule A S`, `scalarExtension φ S` and the same functors on P |
| R_T(1)=mu_N tensor_(Z/N) R, shifted by 2 | `ordinaryFiniteLine R (ell ^ n) hR T`, followed by `⟦(2 : ℤ)⟧` |
| Actual normalized adjunctions F_R ⊣ G_R | `dA`, `dB : OrdinaryFiniteP1Datum ...`; `ordinaryFinitePushforward` and `ordinaryFiniteP1Right` are precisely F_R and G_R |
| K in D^b_ctf(S_et,A) | `K : DerivedCategoryModule A S`, `_hK : ProEtale.AdjunctionTransfer.etaleProperty A S K` |
| Proper coefficient map beta_q | `(scalarMate φ (ProjectiveLine S ↘ S)).app ...`, the geometric counit-transpose proper constituent used by `CoefficientCompatibility.etaleCoefficientMap` |
| Canonical a_K | The explicitly displayed composite of `ExceptionalCoefficients.tensorIso`, inverse `scalarPullbackIso`, `FiniteSmoothPurity.scalarShiftIso`, and shifted `e.derivedIso` |
| Counit equation epsilon_B F_B(a_K) beta_q(G_A K)=T_S(epsilon_A) | The first conjunct, with Lean's left-to-right composition `beta ≫ F_B.map a.hom ≫ dB.adjunction.counit.app ... = scalarExtension.map (dA.adjunction.counit.app K)` |
| Mate of beta inverse on finite-Tor input | Second conjunct: `∃ hβ : IsIso beta`, followed by `a.hom = dB.adjunction.homEquiv _ _ (inv beta ≫ T_S.map epsilon_A)`; this is the componentwise mate bijection, with the same actual B-adjunction |

There are no extra geometric assumptions. The theorem **concludes** the existence
of `hS : IsUnit ((ell^n : ℕ) : Γ(S,⊤))`, rather than adding invertibility as an assumption.
This is implied by the standing field characteristic. It is the proof parameter
required by the published normalized projective-line datum. The theorem also
**concludes** existence of a `CoefficientLineComparison φ N N hA hB P` and then
states the equations for every K and every normalized datum. This introduces the
canonical balanced comparison as data rather than assuming any map or isomorphism.
For N=N>0, its `roots_power` field forces the identity on mu_N (kernel inclusion is
monic and N/N=1). Its `generators` field sends a tensor z to φ(a) tensor z; by
sheafification and the scalar adjunction this determines its ordinary isomorphism.
Its `derived_normalization` fixes the actual derived map using the scalar counit.
Thus the existential isomorphism is uniquely normalized, not an arbitrary choice.
It is fixed before K varies. All normalized P1 data are quantified over, retaining
the exact Kummer class, decomposition, trace and projection-formula counit equation.

Dependency declarations used (module, name):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`; read for the
  standing separated finite-type setting; no condensed category is substituted for
  the ordinary-etale module category here.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the ordinary-etale category).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`; the general K-flat scalar interface.
  `Sheaf.Paper.EtaleDerivedScalarTensor` supplies its existing constant-coefficient
  specialization `AlgebraicGeometry.Etale.scalarExtension`.
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`:
  `AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleProperty`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `AlgebraicGeometry.Scheme.finite_etale_torsion_twist_line`; its underlying line is
  the published `finiteEtaleTateLine`, included in `ordinaryFiniteLine`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`:
  `AlgebraicGeometry.Etale.exists_ordinaryFiniteP1Adjunction`.
  `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data`:
  `OrdinaryFiniteP1Datum`, whose `adjunction` and `counit_normalization` retain the
  actual adjunction and prescribed counit. This owning definition node is added to
  stmt_deps.
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`:
  `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleCoefficientMap` and its
  `etaleProEtaleCoefficientCompatibility` theorem; for proper q the proper map is
  precisely the `scalarMate` constituent, before any identity-open presentation.
- `Sheaf.Paper.PurEtaleScalarMateProjection`:
  `AlgebraicGeometry.Etale.scalarPullbackIso`, `scalarMate`; the owning existing
  node `lem-pur-etale-scalar-mate-projection` is added to stmt_deps.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its representative normalization is retained by the existing specialized comparison
  in `Sheaf.Paper.ExceptionalCoefficientMaps`,
  `AlgebraicGeometry.Etale.ExceptionalCoefficients.tensorIso`; its owning existing
  definition node `def-pur-exceptional-coefficient-normalizations` is added to stmt_deps.
- `Sheaf.Paper.FiniteSmoothCoefficientArrows`:
  `AlgebraicGeometry.Etale.FiniteSmoothPurity.CoefficientLineComparison` and
  `scalarShiftIso`; the existing definition node
  `def-pur-finite-smooth-coefficient-arrows` is added to stmt_deps.

All stated proof-dependency modules are available through the explicit proof imports
or the public statement-dependency imports (proper projection, inverse image
exactness, constructible preimages, finite input models, monoidal comparisons,
projection-mate square). `def-weil-pbc-adjunction-mate` is a Mathlib leaf recorded by
`CategoryTheory.mateEquiv`, available from the projection-mate import.
`lem-sp-p1-splitting-scalar` has no recorded Lean yet and needs no new object to
state this theorem, so there is no module to import for it. No proof dependency
was silently assumed as an additional hypothesis.

Edge cases checked before writing:

- K=0: both morphisms are the unique maps to the zero object, and the same
  adjunction transpose applies.
- S empty: invertibility in its zero section ring and all normalized data remain
  meaningful; no nonemptiness or positive dimension is assumed.
- φ identity: tensor/pullback/shift and root-generator normalizations fix the
  canonical identity comparisons; the formula reduces to the actual counit.
- Nonflat φ: Z/ell²→Z/ell remains included. Scalar extension is derived throughout;
  only the Tate line is flat, and beta invertibility is a conclusion.
- n=0, N=1: the annihilator forces A and B to be zero rings. These are permitted;
  no `Nontrivial` or `n>0` hypothesis is introduced.
- Twists and shifts: +2 is the cohomological shift of the recorded P1 right
  adjoint. Both occurrences use identical comparisons and signs.
- Universes: schemes/k are in u, module coefficients/sheaves in u+1 as in the
  recorded ordinary-etale category. Finite coefficient rings of any smaller
  universe can be lifted; there is no equation of site object/Hom universes.

Searches for an existing statement:

- `msearch.py leanfinder`, query "The actual projective line etale adjunction
  counit commutes with derived extension of finite coefficient rings": 8 hits,
  headed by `StandardEtalePair.homEquiv_symm_apply`,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, and `Algebra.Etale.comp`;
  none states this counit/coefficient identity.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.counit`: 12 hits, including
  abstract adjunction counits, counit extensionality and transport; no geometric
  normalized projective-line coefficient theorem.
- `msearch.py grep`, query `projectiveLine.*(trace|counit)|counit.*projectiveLine`,
  subdirectory `AlgebraicGeometry`: zero Mathlib hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for projective-line counit,
  P1 scalar and the node id: normalized P1 data and the canonical comparison
  helper in `ReductionExceptional` exist, but no exact theorem. That module's
  theorem is downstream of this item in the DAG; it is not imported. The existing
  normalized `CoefficientLineComparison` provides the same balancing without
  duplicating the helper or creating that dependency cycle.
- `rg` for `p1_counit_scalar|p1CounitScalar` in Mathlib, `WeilConjectures` and
  `Sheaf`: no declaration-name conflict. A read-only traversal of the DAG checked
  that none of the four added existing statement dependencies reaches this item.
- The prescribed CompactObject example has been withdrawn and contains no
  declarations in the current checkout; its standard module/public-section format
  is followed, together with the live P1 modules' source/docstring conventions.

No new nodes, dependency-module repairs, statement corrections or disputed
mathematical claims are needed. The only postponed proof is
`AlgebraicGeometry.Etale.p1_counit_scalar`.

Validation: prescribed `scompile.py Q21 lem-sp-p1-counit-scalar` passed cleanly
in both sandbox mode (12.8 s) and the final library module (15.7 s), within the
60-second limit. There are no warnings or errors. Earlier elaboration failures
were diagnosed by an import-only probe and a lowered-heartbeat theorem probe;
the natural common annihilator is now cast explicitly as `((ell ^ n : ℕ) : R)`.
All diagnostic files were removed. The final module contains one named theorem
with `sorry`, no data definitions and no local notation or local instances.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
