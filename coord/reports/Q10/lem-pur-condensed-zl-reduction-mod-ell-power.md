## Worker report

Item: lem-pur-condensed-zl-reduction-mod-ell-power. Module:
`Sheaf.Paper.CondensedZlReduction`. Its eight helper definitions expose the actual normalized
limit projections, the finite residue identifications, scalar multiplication, the module-sheaf
cokernel quotient, its projection, and the residue module with action through reduction. The
one theorem `AlgebraicGeometry.ProEtale.pur_condensed_zl_reduction_mod_ell_power` has proof
`sorry`. No other theorem or axiom is introduced. No node statement or dependency is changed.

Clause-by-clause reading:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The scheme is arbitrary `(X : Scheme.{u})`.
  There is no characteristic or invertibility assumption, and no finiteness, nonemptiness,
  connectedness or quasi-compactness assumption on X.
- Every exponent r >= 1 is written `n + 1`, with `n : ℕ`. All helpers are defined also at
  exponent zero, where the auxiliary tower has the harmless zero-ring term ZMod 1.
- Z_ell is Mathlib `ℤ_[ℓ]`, the norm-at-most-one subtype of the completed field `ℚ_[ℓ]`.
  The condensed sheaf is the recorded `Profinite.continuousMapRingObj ℤ_[ℓ]`, the abelian
  ring object underlying `Profinite.padicIntCondensedRing`. Its sections are ULift of
  continuous functions, with pointwise operations. Its inverse image is the recorded
  `coefficientRing X (Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ]))`, whose underlying
  sheaf is `condensedRingObj ... X`; `sfbPullbackFromPoint` is the alias of this pullback.
- A_(r,X) is `(sfbConstantRing X).obj ((sfbZModCoefficientTower ℓ).obj (op r))`.
  These are the existing constant-sheaf ring objects obtained by the constant sheaf
  functor on abelian groups with its monoidal structure. The coefficients are
  `ULift.{u+1} (ZMod (ℓ^r))`. This is the same constant ring sheaf as the ring-valued
  sheafification, through its standard algebraic-structure presentation; it does not
  replace constants by arbitrary functions on a scheme.
- `purZlReduction` is rho_r. `purZlPointReduction` extracts the normalized point cone
  from the Z_ell/Q_ell clause of `sfb_completed_coefficients`. The reduction is pulled
  back by the existing `upperStarFromPoint`, followed by the theorem's finite-constant
  ring comparison and its normalized `purZlResidueTowerIso`. Thus it is precisely the
  projection in the integral inverse-limit comparison, with quotient presentations
  changed to ZMod as required. It is a bundled ring-object homomorphism, not an arbitrary
  additive arrow.
- `purZlPowerMultiplication ℓ X r` is `ℓ^r • 𝟙` of the regular R_X-module. In an additive
  ring object this is multiplication by the integer scalar ℓ^r. `purZlQuotient` is the
  existing `Mod.cokernelObj` of this map. Its underlying sheaf is the abelian sheaf
  cokernel, not the objectwise quotient presheaf. Hence it is quotient by the image
  ideal sheaf, exactly as in the node. `purZlQuotientProjection` is `Mod.cokernelπ`.
- The existential `m n` gives the quotient its ring-object operations. The first
  `IsMonHom` says that the actual quotient projection preserves unit and multiplication;
  it already preserves addition as a map of abelian sheaves. Since that projection is
  epimorphic and tensor is right exact, this characterizes the usual quotient-ring
  operations uniquely: on local quotient representatives they are the operations
  of `Ideal.Quotient`. No alternative ring structure is substituted.
- `e n` is an isomorphism in R_X-modules from the actual quotient to
  `purZlResidueModule ℓ X (n+1)`. The latter is `Mod.comap` along rho_r of the regular
  A_(r,X)-module, so its scalar action is exactly the action in the node. The next
  two `IsMonHom` assertions say that e and its inverse are also ring morphisms.
  Thus this single comparison is simultaneously a ring and module isomorphism.
- The equation `purZlQuotientProjection.hom ≫ (e n).hom.hom = purZlReduction.hom`
  ensures this is the isomorphism induced by rho_r, rather than just an existence
  assertion that the objects happen to be isomorphic.
- The second universal clause is exactly rho_(r+1) followed by finite reduction equals
  rho_r. Its reduction arrow is the existing `sfbZModCoefficientTower.map`, with
  `homOfLE (Nat.le_succ (n+1))` reversed.
- The final clause gives the quotient transition as an R_X-linear map `t`.
  Its first equation says it is induced by the identity of R_X on quotient classes.
  Its second equation is the commuting square with e and finite reduction. Existence
  is the asserted inclusion of successive image ideals; uniqueness is already part
  of the cokernel projection's epimorphism, so no arbitrary transition is used.

Canonical data and the no-hollow-definition check:

`purZlResidueTowerIso` is extracted from a theorem explicitly specifying its value on
*every quotient class* by `PadicInt.toZModPow`. `purZlPointReduction` is determined by
normalization on constant p-adic inputs and naturality for every point `* → S` of a
profinite set S: finite constant sections are functions determined by these point
restrictions. `purZlConstantPullbackIso` extracts the comparison in ring objects, not
an unstructured additive isomorphism. Each quotient of Z_ell by the indicated power
is a cyclic ring, identified with ZMod by the normalized tower isomorphism. Its constant
ring sheaf is locally generated as a ring by its unit; inverse image preserves this
constant-ring presentation. A unital ring map between two such constant cyclic-ring
presentations is unique, including on each covering object and on the empty object.
Consequently that comparison has no automorphism freedom. All extracted data are
therefore determined up to the equality used downstream, as permitted by AGENTS §5;
no object is selected from an undetermined existence theorem. The cokernel and scalar
action data use the real published constructions, with no sorry inside a definition.
The only postponed mathematical assertion is the node's one named theorem.

Dependency declarations read and used:

- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicIntCondensedRing`; its underlying
  `Profinite.continuousMapRingObj` and commutativity are from the recorded ContinuousMap
  module. Read the definitions and docstrings in the published side framework.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`: `sfbPullbackFromPoint`, its right
  adjoint and specification. The underlying construction `upperStarFromPoint`,
  `condensedRingObj`, and `coefficientRing` were read in the exact framework
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, the
  sheafification of the constant presheaf. Its monoidal presentation here is the
  dependency's `sfbConstantRing` (using the published monoidalConstantSheaf instance).
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient`, `Ideal.Quotient.mkₐ`,
  quotient ring operations and factor maps; `Mathlib.Algebra.Algebra.Hom`: `AlgHom`.
  These underlie the existing quotient tower and the ring-quotient interpretation.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
  Site objects have universe u+1, morphisms u, and coefficient groups u+1; no site
  universes have been identified or restricted to evade an interface problem.
- `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic`; PadicIntegers: `PadicInt`;
  RingHoms: `PadicInt.toZModPow`, `PadicInt.ker_toZModPow`.
- `Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients`: read all helpers, the full
  `SfbCompletedCoefficientComparison` predicate, and `sfb_completed_coefficients`.
  The construction uses its Z_ell comparison, normalized ZMod-tower isomorphism,
  `sfbCoefficientQuotientTower`, `sfbPointConstantRing`, `sfbConstantRing`, and
  `sfbZModCoefficientTower`, without copying any of those notions.
- Proof imports: Mathlib Sites.Limits (`Sheaf.createsLimitsOfShape`),
  Sites.LocallyBijective (`GrothendieckTopology.W_iff_isLocallyBijective`,
  `W_iff` through Sites.Localization), Sites.Sheafification (`presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`), and
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
  (`sheafification_sections_local`). The last was read via `scompile.py --source`.
- The existing `WeilConjectures.CategoryTheory.ModuleObjects.Abelian` supplies the
  concrete sheaf cokernel and induced scalar action; its declarations
  `Mod.cokernelObj`, `Mod.cokernelπ`, and cokernel universal property were read.

Sources and edge cases:

Read both current blueprint units named in the node, including the final E=Q_ell
paragraph of the completed-coefficient proposition. The quotient lemma is the integral
comparison used by the Tate construction, not the unit's separate local-triviality
assertion, so ell-invertibility is not needed. The six-step docstring reproduces the
node's finite-label division, compatible kernel tuple, local lifts, quotient
sheafification, ring/module compatibility, and reduction-square proof.

Checked: r=1 is n=0 and is included; all r>=1 are present, with no assertion at r=0
in the theorem. The auxiliary zero tower term is allowed by the dependency. The empty
scheme has singleton section rings and zero quotient and residue modules, and all
maps and ring assertions remain meaningful. Disconnected and non-quasi-compact
schemes use local lifts and sheaf cokernels, with no sectionwise global-surjectivity
claim. Characteristic ell, mixed characteristic, and ell invertible schemes are all
included. The coefficient lift to u+1 is the published size convention.

Searches for existing declarations (2026-10-18):

- msearch.py LeanFinder: “The quotient of the pulled back condensed p adic integer ring
  by a prime power is the constant residue ring sheaf on the pro etale site”. Eight
  hits: BDeRhamPlus/BDeRham, PadicInt residue-field maps, Witt-vector Fontaine-theta
  maps and PreTilt; none has this sheaf quotient statement.
- msearch.py LeanSearch: “sheaf quotient ring cokernel multiplication by an integer”.
  Eight hits: QuotSMulTop, ring/additive congruence scalar operations, ModuleCat
  cokernel declarations, TopModuleCat.coker; no pulled-back condensed coefficient result.
- msearch.py Loogle: `PadicInt.toZModPow, Ideal.Quotient`: zero hits, with the tool's
  unknown-identifier note for Ideal.Quotient. This is not claimed as evidence that
  ordinary ideal quotient operations are absent; their source definitions were read.
  Repeated with `PadicInt.toZModPow, Function.Surjective`: zero hits, without a tool note.
- msearch.py grep: `Condensed.*quotient|quotient.*Condensed|ker_toZModPow`: seven hits,
  pointwise p-adic kernel calculations and unrelated condensed quotient topology.
- rg in WeilConjectures and lean/Sheaf for the item id, padic quotient combinations,
  and sfbZModCoefficientTower: no existing statement; completed-coefficient tower is
  the relevant dependency. Related finite extension and lisse reduction results concern
  different coefficient models or additional hypotheses and were not reused as this lemma.
- rg in Mathlib Sites and module-sheaf directories for quotient constructions found
  no applicable ring-sheaf quotient declaration. The existing module-object cokernel
  was located in the exact published framework and reused.
- rg for every proposed `purZl` name and the theorem name in WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json found no collision.

No STATEMENT-DISPUTED or node fault was found. No new nodes or dependency repair modules
are needed: the helper data belong to the quotient comparison already introduced by
this item and all general notions come from recorded dependencies.

## Second reading by Q10

This is the author's second reading; the dispatcher requests no separate worker and
maintainer review is independent. Reopened the node and final module. Matched the
prime and arbitrary X with the first two binders and every positive exponent with
n+1. Rechecked the precise R_X and finite constant objects against their dependency
signatures, and traced rho through the normalized point projection and cyclic-ring
comparisons. In particular these are not arbitrary isomorphisms from a Nonempty
existence assertion: the quotient-class normalization and cyclic constant-ring
uniqueness fix all maps. Rechecked that the quotient is a sheaf cokernel, and that
its ring structure is tied to its actual projection, so no unknown ring data or
presheaf quotient replaces the required sheaf quotient. The isomorphism is in modules
with scalar action via rho, has ring-hom conditions in both directions, and satisfies
the induced-map equation. Both successive-reduction clauses were checked with r=n+1:
the reduction equation and quotient-transition square have the correct direction.
The full six-step proof is in the theorem docstring. During compilation I made the
source and target MonObj structures explicit in the three IsMonHom conditions;
this fixes elaboration without changing any mathematical object or hypothesis.
There is no statement correction, extra hypothesis, dropped case or extra conclusion.

Validation: scompile.py passed the final module cleanly (sandbox 6.4 s, named module
27.4 s). The first deliver2.py --no-push passed server preflight and per-file compilation
(commit 20316883db); the final report-only search-log update is checked again below.
