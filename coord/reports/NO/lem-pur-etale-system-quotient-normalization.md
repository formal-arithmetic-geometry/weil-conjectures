## Worker report

Item: lem-pur-etale-system-quotient-normalization, group NO, stage 2.
Module: `Sheaf.Paper.EtaleSystemQuotientNormalization`.

The unchanged node has two paragraphs. The module states the finite-ring paragraph as
`AlgebraicGeometry.Etale.etaleCoefficientQuotientNormalization` and the strict-system
paragraph as `AlgebraicGeometry.etaleSystemQuotientNormalization`. Both proofs are `sorry`.
Their docstrings contain respectively steps 1--4 and step 5 of the node's proof.
The four helper definitions have real construction data and no postponed proofs.
No new nodes, dependency repairs or statement correction are needed.

### Hypotheses and clauses: finite rings

| Node text | Lean rendering |
| --- | --- |
| k is the chosen algebraic closure of F_q of characteristic p | `k : WeilConjectures.FiniteFieldDatum.{u}`; its fields include the prime, finite base field and fixed algebraic closure |
| l is prime and distinct from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ k.p)` |
| X and Y are finite-type k-schemes | `[X.Over (Spec (.of k.k))]`, `[Y.Over ...]`, and `LocallyOfFiniteType` plus `QuasiCompact` for both structure maps |
| f is a separated finite-type k-morphism | `(f : X ⟶ Y) [f.IsOver ...] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` |
| No separatedness assumption on Y | No instance asserting separatedness of the structure morphism of Y occurs |
| Fixed compactification j,p_f | `(c : Compactification f)`; its actual maps are c.i and c.g |
| Finite commutative C,D annihilated by powers of l | `C D : Type (u+1)`, `CommRing`, `Finite`, and `_hC`, `_hD : ∃ r, (l ^ r : ...) = 0` |
| An arbitrary homomorphism C to D | `(a : C →+* D)`; no flatness, surjectivity, injectivity or perfectness assumption |
| Ordinary unbounded étale categories | `Etale.DerivedCategoryModule C W`, the existing derived category of ModuleCat-valued sheaves on W.smallEtaleTopology |
| F_C and F_D | `rightDerivedLowerShriekOfCompactification (ModuleCat ... C/D) c` |
| Arbitrary fixed right adjoints and adjunctions | Explicit gC, gD, adjC and adjD, with no identification to one chosen right adjoint |
| Derived extension T and exact restriction U with canonical scalar adjunction | Existing `scalarExtension a W`, `Sheaf.derivedRestrictScalars ... a`, and `Adjunction.ofIsRightAdjoint` |
| The specified coefficient projection q is an isomorphism | Existential q with `q.hom = compactScalarMap a c`; this records invertibility of the existing projection, rather than assuming an arbitrary invertible square |
| Single-ring restriction comparison r | Existential iso r whose hom is exactly `SystemProjection.singleRestriction (CommRingCat.ofHom a) c` |
| Canonical U^X g_D isomorphic to g_C U^Y | Existential natural iso rho, fixed by its action on every Hom through `quotientRestrictionHomChain`; this chain is the six bijections in step 1, in that order |
| Counit normalization of rho | `F_C.map (rho.hom.app H) ≫ epsilon_C = r.inv.app (gD.obj H) ≫ U^Y.map epsilon_D` |
| b is the specified mate and is invertible | Existential natural iso b with `b.hom = etaleCoefficientQuotientMate a c adjC adjD q`, the real Mathlib mate of q.inv |
| epsilon_D F_D b = T^Y epsilon_C q inverse | The explicit equation `F_D.map (b.hom.app M) ≫ adjD.counit.app ... = q.inv.app ... ≫ (scalarExtension a Y).map (adjC.counit.app M)` |
| Under restriction, b is the constant-tensor map with counit normalization | The last equality conjugates `U^X.map (b.hom.app M)` using `quotientConstantTensorIso`, rho and `gC.map` of the Y comparison; its right side is exactly `adjC.homEquiv _ _ (P.inv.app ... ≫ tensor.map epsilon_C)` |
| The tensor projection is the specified canonical one | P is a natural iso with `P.hom.app K = exceptionalConstantProjectionMap C c (quotientCoefficientComplex a) K` for every K |
| Constant coefficient D[0] | `quotientCoefficientComplex a` is the existing singleFunctor applied to the D-module D with scalars restricted through a |
| Natural on whole unbounded categories | q,r,rho,b,P are natural isomorphisms between the existing full derived functors, and their normalization equations quantify over every object and map, without boundedness premises |
| Independent of resolutions | The scalar functors and `scalarTensorIso` are the recorded canonical derived constructions; `quotientConstantTensorIso` composes those with exact single-complex and constant-sheaf comparisons and the canonical signed symmetry. No resolution or arbitrary tensor identification is a parameter |

The first theorem's additional explicit r, Hom and P equalities expose the canonical
comparisons described by the node, rather than changing any hypotheses. The existential
q and P are uniquely determined by their hom maps; rho is uniquely determined by the
six-Hom formula; b is uniquely determined by the mate equality.

### Hypotheses and clauses: strict systems

| Node text | Lean rendering |
| --- | --- |
| Same geometric setting | The second theorem repeats the same finite-field, over-scheme, finite-type, separated-morphism and compactification binders |
| Finite extension E/Q_l | `E : Type (u+1)`, `Field E`, `Algebra (Padic l) E`, `FiniteDimensional (Padic l) E` |
| O is the ring of integers | `Padic.coefficientExtensionIntegers l E` |
| t is a nonzero nonunit | `_ht : t ≠ 0` and `_hunit : ¬ IsUnit t`; t is not required to be a uniformizer |
| A_n = O/(t^n), n positive | Existing `strictEtaleLevel` uses the ideal `(span {t})^(n+1)`; the index n denotes positive exponent n+1 |
| F_A = Rp_{f,A,*} j_{!,A} | `S : StrictEtaleCompactSupport O t c` and `S.functor` |
| Fixed system adjunction F_A left adjoint to G_A | Arbitrary G and `adj : S.functor ⊣ G`, not B.right |
| Evaluated adjunctions and transition identifications of the evaluation-bound node | B is the recorded Brown comparison package used by that dependency; g and adjN are arbitrary fixed finite-level adjunctions; `_H : StrictEtaleEvaluationBound B adj adjN` supplies theta and its actual transition equation |
| M normalized | `_hM : SheafOfModules.IsNormalizedCoefficientSystem ... S.PY M` |
| G_A M normalized in the same sense | Identical existing predicate applied to `S.PX (G.obj M)` |
| Uses the actual reduction mates | The proof docstring explicitly uses `strictEtaleBrownQuotientMate B adjN h` and H.transition, whose scalar adjoints are exactly the transitions tested by the normalization predicate |
| No false quotient flatness | No `Flat`, `Module.Flat`, Tor bound, boundedness or constructibility premise occurs |

The S and B parameters use exactly the support and comparison presentations of the
recorded evaluation-bound interface. Brown construction supplies B for every S; it is
not a new geometric hypothesis or a restriction to a specially chosen system adjoint.
The system theorem assumes the evaluation/transition package as the node explicitly does.
The finite-ring theorem gives the actual nonflat mates used in its proof. The normalization
predicate already quantifies over all m,n with n ≤ m, including m=n.

### Dependency declarations used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its field instances.
- Scheme-morphism convention: Mathlib `Scheme.Over`, `Scheme.Hom.IsOver`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `WeilConjectures.Compactification.RefinementCategory`: the existing Compactification
  and Refinement interfaces (only Compactification is needed in this statement).
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  the theorem quantifies over fixed adjunctions to this existing functor.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings` and the public generic ringed-site
  construction; the ordinary étale presentation is the existing `Etale.scalarExtension`
  and representative-normalized `Etale.scalarTensorIso` from the transitively imported
  `Sheaf.Paper.EtaleDerivedScalarTensor`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; the small-étale scalar adjunction
  is the recorded `Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars ...)`.
- `Sheaf.Paper.EtaleSystemCoefficientProjection`:
  `AlgebraicGeometry.Etale.SystemProjection.etaleSystemCoefficientProjection`,
  `Etale.compactScalarMap` and `Etale.SystemProjection.singleRestriction`.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor`:
  `Etale.exceptionalCoefficientTensor`, `Etale.exceptionalConstantProjectionMap`,
  `Etale.exceptionalConstantTensor`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the publicly reexported coefficient data.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`:
  `SheafOfModules.coefficientSystemDerivedComparison` and
  `SheafOfModules.IsNormalizedCoefficientSystem` (defined in its public ImageData module).
- `Sheaf.Paper.EtaleSystemEvaluationBound`: `StrictEtaleEvaluationBound`,
  `strictEtaleBrownQuotientMate`, and `etaleSystemEvaluationBound`; its publicly imported
  Brown and strict-system interfaces supply S, B and the actual system/level categories.
- Proof imports: `SheafOfModules.exists_changeOfRings_tensor_comparison` from
  `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`,
  `SheafOfModules.restrictScalars` from Mathlib's sheaf ChangeOfRings module,
  and `CategoryTheory.mateEquiv` from Mathlib's Adjunction.Mates module (also directly
  used by the real mate helper).

### Searches and source reading

- msearch.py leanfinder: `Derived exceptional inverse image commutes with nonflat finite
  coefficient quotients and preserves normalized strict systems`. Eight unrelated hits:
  scheme normalization, smooth-flat algebra and cotangent/faithfully-flat exactness;
  none states this result.
- msearch.py loogle: `CategoryTheory.mateEquiv`. Twelve hits identify the general mate
  construction and its unit/counit laws. Reused, but it does not assert invertibility
  of this exceptional coefficient mate.
- msearch.py grep: `quotient.*normaliz|normaliz.*quotient|exceptional.*[Cc]oefficient`,
  subdirectory CategoryTheory. One unrelated free-monoidal coherence hit.
- msearch.py leansearch: `exceptional inverse image nonflat coefficient quotient
  normalization`. Eight scheme-normalization hits; no relevant declaration.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id and for
  `quotientNormalization|etaleSystemQuotient|NonflatCoefficient|nonflat.*mate` found no
  declaration of the whole item. All six proposed names were separately checked
  against those roots and Mathlib and were absent.
- Read the complete recorded signatures/docstrings of all statement dependencies,
  the evaluation-bound and Brown comparison structures, the scalar tensor iso and
  constant tensor projection; read Mathlib's mateEquiv and sheaf restrictScalars.
- Read Zheng PDF printed p.16 Proposition 2.29(2), printed pp.36--37 Lemma 5.22,
  its following weak-normalization sentence, and Proposition 5.24. Also read the current
  blueprint's exceptional-inverse-image definition in literature/blueprint/latest.
  The node explicitly defines normalized by transitions, the weak-normalization condition;
  it does not assert the stronger unbounded completion condition called normalization
  elsewhere in Zheng. No correction to the node is required.

### Edge cases and validation

Checked identity ring map, C=D, D=0, zero module input, X empty and Y empty. No
nontriviality or nonempty scheme is required. The nonflat example Z/l^2 to Z/l is
included without additional hypotheses. An exponent r=0 in annihilation is allowed
and forces the zero ring, which is also covered. Arbitrary unbounded input is allowed.
For systems, m=n is included, as is any nonzero nonunit t=u*pi^r with r>1.
The comparison tensor uses D as a C-module, never assumes it has finite projective
dimension. Scheme universes are u, constant-module coefficients u+1, and strict
system derived categories u+2, exactly as in the dependency interfaces.

Compiled with scompile.py in module mode: both sandbox and real library-path checks
succeeded. The first compile identified an unregistered IsIso instance needed by a
bare inverse of singleRestriction; the conclusion now exposes the canonical restriction
iso r and uses r.inv. The existing normalization predicate also needs its four universe
arguments explicitly at the étale site sizes; these were supplied. A field-notation
line break in the singleFunctor comparison was corrected. No theorem was proved.

## Second reading by NO

A separate in-thread rereading checked the node against the complete final Lean file.
The dispatcher explicitly prohibits starting other agents, so this section does not
claim an independent worker review; the delivery proceeds to the maintainer's independent
review as specified in the assignment.

The first paragraph is covered by the first theorem, rather than only by the main
system declaration: both names are listed in lean.declarations. The fixed adjunctions
remain arbitrary. q is constrained to compactScalarMap; rho is constrained by all six
Hom bijections; b is constrained to the actual mate and has the exact requested counit
equation. The final tensor equality starts from coefficient-first tensor, inserts the
inverse scalar/tensor identification, applies U(b), rho, then g_C of the Y identification.
Its target and counit transpose agree with the node. This verifies the orientation of
q inverse and of both rho and tensor comparisons. No arbitrary isomorphism replaces
the constant projection: P has its component equation for every K.

The second paragraph uses the existing strict systems and the existing transition
normalization predicate on both sides, with the same ring and t. H contains the actual
transition equation, and the docstring uses that equation, not a family of unrelated
level isomorphisms. Its g_n and G are independent fixed choices. There is no separatedness
of Y, flatness of coefficient maps or boundedness of M. No missing clause, statement
fault or STATEMENT-DISPUTED issue was found in this rereading.
