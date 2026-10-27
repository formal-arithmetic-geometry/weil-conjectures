## Worker report

The module `Sheaf.Paper.IntegrationTransposeComposition` states
`AlgebraicGeometry.Etale.IntegrationComposition.integrationTransposeComposition`.
Its sole theorem is postponed with `sorry`. Nine helper definitions have real data:
`object`, `integration`, `gamma`, `unitObjectIso`, `orientation`, `theta`,
`pullTensorIso`, `reassociation`, and `rightMate`. All belong to this node's
integration/transposition construction and are listed in `lean.declarations`.
One definition-only node now records the two unchanged published compact-support projection maps. No new Lean definition or dependency module is needed.

I read the current node, all nine original statement-dependency nodes and their
recorded source declarations/docstrings, the eight proof steps, and the source
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md`,
paragraph 2. The prior Q65 delivery is a stage-1 proof split; it attaches no Lean
statement. This stage-2 packet preserves that split and the node's statement verbatim.

The exact hypothesis/clause audit follows. Lean composition `≫` is diagrammatic,
so a displayed mathematical composite is read from right to left in the source
and from left to right in Lean.

| Node's hypothesis or clause | Lean rendering |
| --- | --- |
| Finite commutative coefficient ring A | `{A : Type (u + 1)} [CommRing A]`, with `[Finite A]` on the theorem |
| Noetherian schemes X, Y, Z | `{X Y Z : Scheme.{u}}` and `[IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]` |
| Composable separated finite-type maps f, g | `(f : X ⟶ Y) (g : Y ⟶ Z)`, each with `[IsSeparated] [LocallyOfFiniteType] [QuasiCompact]` |
| Compactifiability of f, g and h=gf | The three `HasCompactification` binders, with `h` written `f ≫ g` |
| Ordinary small-etale unbounded categories | Every object and functor uses the recorded `DerivedCategoryModule A T`, never the pro-etale or constructible categories |
| Compact-support functors Ff, Fg, Fh | `rightDerivedLowerShriek (ModuleCat.{u + 1} A) f`, likewise g and `f ≫ g`; these use the recorded chosen-compactification construction |
| Actual right adjoints Rf, Rg, Rh | Three functor binders and the three specified adjunctions `adjf`, `adjg`, `adjh`; no property of an arbitrary comparison map is assumed |
| Proper/open triangle-normalized alpha | Exactly `unboundedEtaleLowerShriekCompIso A f g` |
| Adjunction-preserving right mate c | `rightMate`: transport `adjf.comp adjg` along alpha with `ofNatIsoLeft`, then use `adjh.rightAdjointUniq`; this is the canonical adjunction-preserving isomorphism, including its inverse |
| Composite Hom bijection | Mathlib `Adjunction.comp` is used by `rightMate`; its Hom equivalence is the composite of the two recorded bijections |
| Chosen Wf and Wg | The two unrestricted derived object binders |
| Wh=f*Wg tensor Wf | `object f Wf Wg`; `object` uses the exact termwise `upperStar.mapDerivedCategory` and the recorded `derivedTensor` |
| Traces tf, tg, th | The three morphism binders, with target the derived tensor unit, the recorded constant coefficient sheaf in degree zero |
| Canonical proper/open projection P | Existing `compactSupportProjectionMap A f W K`; its existing definition is the proper/open projection, reordered by signed symmetry and the exact-pullback comparison |
| Invertibility on all coefficient inputs | `hPf`, `hPg`, `hPh` quantify over every object of the appropriate unbounded category with Wf, Wg, Wh respectively |
| Composite trace equation | `ht`: `alpha.hom.app Wh ≫ th = Fg.map (integration f Wf tf hPf Wg) ≫ tg` |
| Integration `(1 tensor t) P⁻¹` | `integration`: inverse P, then `(derivedTensor ...).obj K` applied to t, then the canonical right unitor |
| gamma is the actual transpose | `gamma` is `adj.homEquiv _ _ (integration ...)` |
| Reassociation a_K | `reassociation` first uses `unboundedEtaleUpperStarCompIso`, then the inverse canonical derived associator, then inverse exact-pullback tensor comparison, in the stated order |
| Composition equality | First conjunct is `gamma_h = a.hom ≫ (f*gamma_g tensor 1) ≫ gamma_f(Rg.obj K) ≫ c.inv.app K` |
| omega_f=Rf(A_Y) | Written directly `Rf.obj (𝟙_ _)`, with no second dualizing object |
| theta is the transpose of inverse projection followed by the counit | `theta` uses `adj.homEquiv`, inverse `compactSupportProjectionMap` at omega, tensoring `adj.counit.app (𝟙_ _)`, and the right unitor |
| theta is defined whenever its projection is invertible | Second conjunct quantifies over L and a proof `hPomega` for exactly that L; no all-input invertibility or orientation-isomorphism hypothesis is added to this clause |
| theta(1 tensor gamma_at_unit)=gamma_L | Second conjunct; `orientation` is gamma at the unit after `unitObjectIso.inv`, which explicitly supplies the source's implicit identification `f* A_Y tensor Wf ≅ Wf` |
| Vector-bundle specialization Wf=A_X(r)[2r], Wg=A_Y(s)[2s] | Third conjunct quantifies N,r,s and `(N : A)=0`, then the two equalities with `DerivedCategory.singleFunctor` applied to the existing ordinary `Scheme.finiteEtaleTateTwist`, shifted by `2 * (r : ℤ)` and `2 * (s : ℤ)` |
| Invertible orientation makes projection with omega invertible | Third conjunct assumes `IsIso (orientation ...)` and concludes `∀ L, IsIso (compactSupportProjectionMap A f (Rf.obj (𝟙_ _)) L)` |
| Ambient input Rg K is included | L ranges over all unbounded objects, in particular `Rg.obj K`, which is used explicitly by the first conjunct; there is no boundedness, constructibility, or Tor hypothesis on that object |
| Even-shift block-interchange sign is 1 | Fourth conjunct is `∀ r s : ℕ, (-1 : ℤ) ^ ((2 * r) * (2 * s)) = 1`; the reassociation helper itself contains no braiding or interchange |

The N and annihilation binder in the specialization expose the parameter of the
already-landed ordinary finite Tate-twist definition. They are local to that
specialization and do not restrict the general composition or theta identities.
All finite rings admit an annihilator, including the zero ring. This does not
assert or assume a Tate orientation; the orientation remains the specified
actual transpose of the trace. No invertibility of N on the schemes is added.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, `rightDerivedLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`; the theorem's
  specified actual adjunctions are retained rather than replacing them with a
  choice of right adjoint.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleUpperStarCompIso`.
- `Mathlib.CategoryTheory.Adjunction.Basic`, `.Unique`, `.Mates`:
  `Adjunction.comp`, `Adjunction.ofNatIsoLeft`, `Adjunction.rightAdjointUniq`,
  `Adjunction.homEquiv`, and the canonical mate convention of `mateEquiv`.
- `Sheaf.AlgebraicGeometry.ShriekTensorComposition`:
  `compactSupportProjectionMap`, `compactSupportProjectionMap_comp`.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`:
  `isIso_proper_projection_formula_reordered` (the recorded proper projection).
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  `derivedOpenImmersionLowerShriekProjectionIso` (the recorded open comparison).
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and `.TensorStructure`:
  `derivedTensor`, `derivedTensorAssociator`, `derivedTensorLeftUnitor`,
  `derivedTensorRightUnitor`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `leftDerivedUpperStarTensorIso`, `leftDerivedUpperStarUnitIso`, and
  `leftDerivedUpperStarIsoMapDerivedCategory`. The helpers transport these
  canonical isomorphisms to exact termwise inverse image, never an arbitrary map.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateTwist` for the literal specialization.
- The five private proof imports are the recorded normalized additive tensor
  constraints, exact pullback signed comparison, pullback-composition monoidality,
  ringed projection tensor composition, and total tensor signed coherence.
  `LowerStarProjection` is also imported for the recorded counit-defined
  proper projection used in the proof plan. The theorem docstring gives all
  eight proof steps, with only the final theorem left as `sorry`.

The item's `stmt_deps` cites the new definition owner
`def-pur-compact-support-projection-map`, together with the already-landed
`lem-kun-inverse-image-monoidal`, `lem-kun-tensor-unit`,
`def-asd-finite-etale-tate-twist`, `def-sf-etale-support-compositor`, and
`def-pur-etale-exact-pullback-unit-composition-comparisons`. These own the
canonical projection, tensor comparison, unitors, finite twists, proper/open
compositor, and exact pullback unit/composition comparisons actually used.
`lem-amb-shriek-tensor-composition` stays a proof dependency only. No dependency
node or published dependency module is changed.

Edge cases checked by mathematical reading: empty schemes and zero objects are
allowed by every binder; no Nonempty, nonzero coefficient, or characteristic
restriction occurs. With f and g identities the formula is the iterated trace
transpose with the normalized unit compositors. A zero trace is permitted, and
the theta identity does not require its orientation to be invertible. Ranks
r=0 or s=0 use the constant degree-zero twist and the sign is 1. The third
clause is conditional on the actual orientation being invertible; it does not
assume purity in order to define gamma or theta. Objects Rg K and arbitrary
unbounded complexes are never silently placed in a constructible category.

Searches performed before writing:

- msearch LeanFinder: `Adjoint transpose of integration trace and projection formula is compatible with composition of compact support functors`:
  eight hits, all unrelated compactly supported continuous-map/integration results.
- msearch Loogle: `CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.rightAdjointUniq`:
  zero combined hits. Read Mathlib's actual declarations directly; they supply
  composition and the unique normalized right-adjoint comparison, not this node.
- msearch Mathlib grep: `integrationTranspose|integration_transpose|compactSupportProjection`:
  zero hits.
- msearch LeanSearch: `Adjoint transpose integration projection formula compatible with composition compact support derived categories`:
  eight linear-map/inner-product adjoint-transpose results, none about etale functors.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for integration/transpose/composition
  and compact-support projection names; exact blueprint-id search in both trees;
  `dag/lean_names_upstream.json` for `integrationTransposeComposition|IntegrationComposition`.
  No existing theorem states this node. The existing `ShriekTensorComposition`
  provides the canonical projection and composition law, and is reused.
  `IntegrationTransposeScalarMate` states scalar change, with a specified
  compactification and left-derived pullback endpoints; it does not state
  composition, the unit/dualizing identity, or this node's exact-pullback maps.
  The local helpers therefore only assemble the specified exact-endpoint maps.

Compilation uses only the prescribed scompile.py wrapper. An initial direct use
of concrete monoidal notation made kernel conversion unfold large derived
constructions. Replacing it with the existing explicit derived-tensor bifunctor,
its maps and its canonical unitors removed that conversion cost. The complete
module then compiled cleanly in sandbox and library modes (13.3 s and 14.9 s).
The initial repair dry run also passed against the current server library. Final repair validation is recorded below.

No STATEMENT-DISPUTED flag or statement correction is needed. No source statement,
proof, or proof dependency was changed, and the Q65 reviewed split is preserved.

## Second reading by Q49

This is a separate clause-by-clause pass by the same worker; the dispatcher
explicitly forbids starting another agent and the maintainer performs the
independent review. I reopened the complete node and finished file and checked
the trace-composition direction, right-mate direction Rh to Rf Rg, and the order
of every arrow in the first conjunct. The unit orientation originally had an
implicit source identification; the final `unitObjectIso` makes it explicit.
The final theta clause permits each individual L with an invertible projection,
without requiring orientation invertibility. The invertibility-transfer clause
is restricted explicitly to the stated Tate-twist/even-shift specialization,
and the actual ordinary twists are reused. The finite-ring, Noetherian,
compactifiability, separatedness and finite-type hypotheses are all retained.
The sign quantifies over nonnegative ranks including zero. The source statement
is unchanged. All nine definitions are compositions or evaluations of existing
canonical constructions; only the node's named main theorem has `sorry`.


## New nodes

`def-pur-compact-support-projection-map` is a definition-only ownership record
for `AlgebraicGeometry.Etale.compactSupportProjectionMapOfCompactification` and
`AlgebraicGeometry.Etale.compactSupportProjectionMap`, both unchanged plain
noncomputable definitions in `Sheaf.AlgebraicGeometry.ShriekTensorComposition`.
Its `lean` is `existing: true`, with no new module. Its statement spells out
all four arrows: signed symmetry to the coefficient-last convention; the
proper/open projection; exact-pullback comparison in the second tensor factor;
and inverse signed symmetry inside the compact-support functor. The chosen
version evaluates the same construction at
`HasCompactification.compactification f`. This is the projection used in
integration in paragraph 2 of the source blueprint. It asserts no projection
isomorphism or composition law. Its general commutative-ring and arbitrary
compactification interface agrees with the existing definitions; no finite,
Noetherian, boundedness or Tor condition is added. The specified version does
not require a chosen-compactification instance. Empty schemes, zero objects
and the zero ring are allowed; no projection inverse occurs in either map.

The searches for this node were actually rerun during repair:

- LeanSearch, `Canonical compact support tensor projection map constructed from proper direct image and open extension by zero`: eight hits about compact support of functions and test functions, none about etale categories.
- LeanFinder, `Compactification construction of the coefficient first compact support projection formula morphism`: eight hits in the Nobeling proof for profinite spaces, none about this map.
- Mathlib grep, `compactSupportProjectionMap|projectionMapOfCompactification|rightDerivedLowerShriek`: zero hits.
- `rg` of the same map names in `lean/WeilConjectures` and `lean/Sheaf`: upstream `LowerShriekProjection` gives the coefficient-last proper/open projection; the two exact coefficient-first definitions are at lines 149-192 of `ShriekTensorComposition.lean` and are reused.
- DAG search by the declaration name: only `lem-amb-shriek-tensor-composition` listed these declarations. No definition node owned them. Definition candidates for pro-etale, rational, condensed and primary-coefficient projections have different data; in particular `def-weil-compact-support-coefficient-action` uses rational/adic coefficient realizations.
- `tools/blueprint_refs.py search 'compact support projection'`: zero blueprint-node matches. `search 'projection map'`: 23 candidates, none owns these general coefficient-first ordinary-etale maps. `ancestor lem-pur-integration-transpose-composition` returns `cor-pur-vector-bundle-purity`; the new node records that ancestor with the item prepended to `via`.

## Repair of return L at 4203bbe51a4f

H2/H12: added the definition node above, exactly as requested. Replaced the
saved packet's statement dependency `lem-amb-shriek-tensor-composition` by
`def-pur-compact-support-projection-map`; the former remains in the original
`proof_deps`. The new record lists both existing projection maps and binds the
chosen map's signature verbatim. No theorem is used to define those maps.
The theorem file, source statement, proof steps and proof dependencies remain
unchanged from the returned packet. Comparing the saved packet against the
current read clone found only the intended Lean attachment and added statement
dependencies; the delivery wrapper rebases it on the current server branch.

Advisories: cited `def-sf-etale-support-compositor` and
`def-pur-etale-exact-pullback-unit-composition-comparisons` as existing owners.
The unit half of `unitObjectIso` is the exact construction recorded by
`etaleSumPullbackUnitIso`; the helper then tensors this comparison with W and
applies the left unitor. `rightMate` and `etaleSumRightAdjointCompIso` express
the same canonical adjunction-preserving comparison: the former uses
`ofNatIsoLeft` and `rightAdjointUniq`, the latter `conjugateIsoEquiv`. This is
reported as the H4 advisory, preserving the reviewed theorem and helper API.
The last conjunct is precisely the arithmetic even-block sign, as reviewed.
The six private imports are retained because they are the recorded proof-plan
imports required by stages/2-statements.md section 3 rule 7, even though the
stage-2 sorry body does not yet refer to their declarations. Each is a listed
proof dependency, not an incidental unused import.

Second reading of the repair by Q49: reopened the node, the finished Lean file,
the new node and both existing projection definitions. The new definition
statement has the same source and target as each existing definition and the
same four arrows in order. The definition record has no file, no new theorem,
no chosen existence witness, and no composition-law hypothesis. The item
names it in `stmt_deps` and still names the composition theorem in
`proof_deps`. The proper/open and exact-pullback comparisons now cite their
existing definition owners. The main theorem's hypothesis/clause table above
is unchanged and still matches each binder and all four conjuncts. The
projection direction, theta identity, arbitrary ambient inputs and rank-zero
cases agree with the independent maintainer review. No statement correction
or STATEMENT-DISPUTED flag is needed.


## Final repair validation
The unchanged theorem module compiled cleanly through scompile.py against the live published build: sandbox mode 15.6 s and library mode 14.0 s, exit 0. The final self-check confirms the original node statement, proof steps and proof dependencies are unchanged, the Lean signature is verbatim, both existing projection declarations have definition ownership, and the main theorem is the sole sorry.
