## Worker report

The module `Sheaf.Paper.FiniteTripleProductNormalForms` states
`AlgebraicGeometry.ProEtale.finiteTripleProduct_normalForms`. Its proof is `sorry`.
Every helper has real data: the product geometries, forward maps, ordinary maps,
open comparisons, restriction identifications, and coordinate comparisons are
composites or specializations of existing declarations. The item's mathematical
statement and Lean file are unchanged by this repair. The statement now cites
`def-pur-finite-product-compactification-data` for the binary data and the landed
`def-pur-finite-ordinary-product` for Omega. The binary comparison theorem remains
a proof dependency only.

Hypotheses and clauses, checked against the node:

- The finite field, distinct primes, finite coefficient extension and positive
  level are exactly `C : WeilConjectures.PurityFiniteSetting`; coefficients are
  `C.Coefficient`, the existing standard size lift of O_E/(varpi^level).
- Each of `B,X₁,X₂,X₃` has its `Over (Spec (.of C.field.k))` instance and
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on its structure map.
  These express separated finite type over the fixed field. The corresponding
  three classes and `IsOver` are bound on each `f₁,f₂,f₃`.
  The compactification objects carry the actual open inclusions and proper
  ambient maps; their ambient schemes inherit the standing geometric properties.
- The ordinary unbounded constant-module categories are `FiniteTripleProduct.D`,
  an abbreviation of the existing `FiniteD`. The small pro-etale sites retain
  object universe u+1 and morphism universe u. Coefficient modules have universe
  u+1. `tensor`, `external`, `extend`, `support` only specialize the existing
  finite-coefficient operations, without installing a different category.
- The specified Xi is `xi`, whose body is `finiteProductChosenForward` with its
  actual two signed symmetries, PF, Ex_!, PF and normalized composition map.
  Compactifiability instances inside this helper come from the supplied
  compactifications, not extra existence assumptions.
- The specified ordinary Omega is `finiteProductOrdinary`, the same
  counit-defined ordinary word in fixed-scalar coordinates, including the inverse
  `finiteDirectImageComposition`. `FiniteProperProductTranspose` supplies the
  intrinsic presentation of that same word; the binary compactification module
  already gives its fixed-scalar representative, so it is used rather than copied.
- `M₁,M₂,M₃` are the recorded `DerivedCategory.Plus` objects and `w₁,w₂,w₃`
  are `Scheme.FixedEtaleOriginWitness`. Their retained etale antecedents and
  actual comparison isomorphisms give the origin-class arguments. They are not
  replaced by arbitrary maps, abstract operations, or bounded constructible inputs.
- `c₁,c₂,c₃ : Compactification fᵢ` are arbitrary displayed compactifications.
  `g12,g23` are `finiteProductGeometry` on the actual Mathlib pullbacks.
  `gL,gR` repeat it with `finiteProductCompactification` on the inner product.
  Thus the product opens and proper maps are the actual geometric constructions.
  `d12,d23,dL,dR` are the corresponding external tensor objects.
- `b₁₂,b₂₃,bL,bR` are exactly four instances of the recorded
  `FiniteProductCompactificationDomain`, one for each binary or iterated forward
  word. Each enumerates its source tensor, its reversed source, the two tensors
  around the internal symmetry, the exchanged tensor and the external tensor.
  Every entry is the bounded-below etale-origin property. `_sL,_sR` additionally
  require that property on the two initial three-factor source tensors, which
  are not themselves source objects of the outer binary word. There is no Tor interval,
  constructibility hypothesis, exceptional adjoint or six-functor datum.
- H_i is `(extend C.Coefficient cᵢ.i).obj Mᵢ.obj` throughout. `e12Source`
  and `e23Source` are the recorded `finiteProductExtendedTensor` objects.
  `eLSource,eRSource` name the respective ambient triple external tensors.
- `eL` is exactly external tensor of `finiteProductOpenTensor` for (1,2) with
  identity, then the outer `finiteProductOpenTensor` for (12,3). `eR` is the
  analogous right composite. These binary maps already include the normalized
  open-extension compositor. They are the same normalized maps as
  `FiniteOpenProduct.comparison`: their specified restriction is the identity,
  which determines a morphism into open extension uniquely by full faithfulness.
- `Equations` explicitly asserts `IsIso eL` and `IsIso eR`. It also asserts their
  two restriction equations. `restrictPair` is built only from the geometric
  projection identities, canonical pullback compositors and tensor-pullback
  comparison; `restriction12,restriction23` insert the two actual open units.
  `restrictionL,restrictionR` recurse with the third unit. Thus these restriction
  identifications do not use eL, eR, or their inverses to define themselves.
  `openAdj` transports the existing exact open adjunction to total-derived
  pullback coordinates with its existing canonical comparison.
- `thetaL` and `thetaR` are the two displayed Xi iterates, followed by the
  normalized comparison of the original final compactification to the displayed
  product compactification. The displayed candidate is definitionally Rc_*u_!.
  `ordinaryL` and `ordinaryR` are their respective Omega iterates, followed by
  Rc_*(eL) and Rc_*(eR). The final two conjuncts of `Equations` are exactly
  `thetaL = sourceL ≫ ordinaryL` and `thetaR = sourceR ≫ ordinaryR`.
- `sourceL,sourceR` tensor the three actual normalized endpoint comparisons.
  All displayed cᵢ and all original oᵢ, o₁₂, o₂₃, oL, oR are independently
  universally quantified. Hence both equalities hold in every original coordinate
  system with the same normalized comparison functors, including every refinement.
  Their common-refinement independence and cocycle are precisely the existing
  comparison interface, not additional hypotheses. In particular the original
  and displayed choices are not forced to coincide.
- Each bracketing uses its own actual iterated Mathlib pullback. These are the
  two canonical representatives of the node's triple product, identified by its
  universal property. The node asserts separate equations, with no equality
  between the two Xi or Omega iterates. Stating each equation in its own
  representative therefore retains the full assertion without requiring an
  additional reassociation theorem as an assumption.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, its ring and finite-coefficient instances.
- `def-weil-scheme-morphism-properties` is explicitly a convention record,
  with no declaration of its own. Its relevant Mathlib classes are
  `AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsOpenImmersion`, `IsProper`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback` and
  `finiteIntrinsicDerivedTensor`, read with their K-flat-normalized definitions.
  The existing binary module uses the canonical fixed-scalar representatives
  `ProEtale.derivedTensor` and `L(upperStar ...)`; those are used consistently.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingDerivedPullback` and its canonical ring comparison;
  the ordinary fixed-scalar operations are the presentation already supplied by
  the binary and open-product dependencies, not a new coefficient construction.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `IsPullback.lift`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `compactificationExchangeFromData`, `compactificationProjectionFromData` and
  `ExchangeProjectionStage` describe the actual mates. The binary dependency
  specializes these as `finiteForwardProjectionMap`,
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, and the ordinary
  `finiteProductOrdinaryProjection`/`derivedBaseChangeMap`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originCompositionAmbient`, used by `finiteProductComposition` inside Xi.
- `Sheaf.Paper.FiniteProperProductTranspose`:
  `WeilConjectures.FiniteProperProduct.omega` and
  `finiteProperProductTranspose`; the ordinary fixed-scalar word used here is
  already provided as `finiteProductOrdinary`, owned by
  `def-pur-finite-ordinary-product`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `Scheme.FixedEtaleOriginWitness`, including `.complex` and `.iso`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `Compactification.Refinement`, its category and actual refinement triangles.
- `Sheaf.Paper.CompactificationCoherence`:
  `compactification_coherence`. The source and target transports are its
  normalized origin-class form `finiteForwardCompactificationComparison`,
  supplied by `Sheaf.Paper.FiniteForwardProductSymmetry`.
- `Sheaf.Paper.FiniteOpenProductSwap`:
  `WeilConjectures.FiniteOpenProduct.comparison`, `finiteOpenProductSwap`;
  compared with the already supplied `finiteProductOpenTensor`, not redefined.
- `Sheaf.Paper.FiniteProductCompactification`:
  `FiniteProductGeometry`, `finiteProductGeometry`,
  `finiteProductCompactification`, `finiteProductExternal`,
  `finiteProductExtendedTensor`, `finiteProductOpenTensor`,
  `finiteProductChosenForward`, `FiniteProductCompactificationDomain`,
  `finiteProductOrdinary`, `finiteProductPullTriangle`, and tensor-map helpers.
  The binary data are now owned by the new definition node below, with
  `finiteProductOrdinary` separately owned by `def-pur-finite-ordinary-product`.
  The theorem `finiteProduct_compactification` is the two-step proof input only;
  its conclusion is not used to introduce any statement data.
- Proof imports also retain the recorded derived tensor-pullback and open
  extension composition modules. The theorem docstring gives all five DAG steps.

Edge cases checked before and after writing:

- Empty schemes or an empty factor remain allowed; the geometric universal
  properties and the maps still exist, and no nonemptiness binder was introduced.
- Zero inputs are allowed, and the forward products remain maps rather than
  assumed isomorphisms. No cancellation of exchange or projection is built in.
- Proper f_i and identity opens reduce to the ordinary product coordinates;
  identity refinements give the existing identity comparisons. Repeated choices
  of compactification are allowed by the independent universal quantifiers.
- Positive level n=1 is included. Level zero is excluded exactly by the existing
  purity coefficient conventions. Equal residue and coefficient characteristics
  are excluded exactly by the original distinct-prime datum.
- Odd cohomological shifts retain the signed derived symmetry in each Xi/Omega;
  none is replaced by an unsigned tensor flip.
- Both left and right outer domains are required: D12 and D23 each have their
  own origin condition from the corresponding binary domain. No boundedness of
  auxiliary proper ordinary tensor objects is imposed.
- A change in one, two or all three compactifications is allowed, as are changes
  of the intermediate and output original choices. The normalized transports
  stay on the origin domain, never on all unbounded complexes.

Searches actually run (msearch.py, NZ/item, plus read-only rg):

- LeanFinder: "Iterated compact support external products of three derived
  sheaves equal ordinary proper products on the triple compactification".
  Eight hits: generic categorical external-product comparison components,
  condensed monoidal categories, and condensed finite-product preservation.
  None is this geometric derived normal-form statement.
- Loogle: `"pushforward", "tensor"`. Zero hits.
- LeanSearch: "Triple compact support derived sheaf products computed using
  proper compactifications". Eight hits on compact support of functions and
  finite products in sheaf categories. No match.
- msearch grep of Mathlib CategoryTheory:
  `triple.*[Cc]ompact|[Cc]ompact.*triple|[Tt]riple.*[Nn]ormal`. Zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` with that regexp found unrelated
  Fourier kernel triple products, ordinary compactification composition seed
  statements, and the supplied open product coherence criterion. None states
  the two specified finite compact-support normal forms. rg of the chosen
  declaration names found no collision. The upstream item-ID grep had no hits.
- Read `lem-sf-triple-compactification-normal-form`: no Lean record, and it uses
  an abstract six-functor datum, finite Tor and bounded constructible inputs,
  unlike the present ordinary finite-level statement; it is not a usable match.
- Read the newest `literature/blueprint/latest/.../lem-sf-kunneth-coherence.proof.md`
  in full. Clause (ii), the compactification-reduction sentence and the accepted
  concrete five-step DAG proof give the stated calculation.

No STATEMENT-DISPUTED issue or source-based correction was needed.

## Second reading by NZ

A separate rereading pass by this dispatcher-started worker, without spawning
another agent as the brief explicitly prohibits, compared the node and Lean file
clause by clause. Independent mathematical review remains the maintainer's.
The pass verified all four geometric hypotheses lists, all three retained input
witnesses, all four complete tensor domains, both open-isomorphism and restriction
conjuncts, both separate normal forms and the independent compactification choices.
It checked the actual eL/eR definitions and both ordinary words against the displays,
including both signed symmetries and the inverse ordinary compositor. It also checked
that restrictionL/R use only the three units and canonical pullback/tensor comparisons,
so the normalization assertions are not tautologies. The pass added the two initial triple-source tensor domain hypotheses `_sL,_sR`;
they are required by the node and are not silently inferred from bounded-below
inputs. An initial local spelling of
`finiteProductExtendedTensor` was corrected to the recorded declaration; unused
geometric arguments were removed from `externalMap`. No mathematical change was made.


## New nodes

`def-pur-finite-product-compactification-data` is a definition node in
`sec-smooth-purity`, registered with `existing: true` on
`Sheaf.Paper.FiniteProductCompactification`. Its self-contained TeX defines the
three Cartesian products, two open lifts, product compactification, external and
extended tensors, tensor/open actions, pullback triangles, open base change and
composition, two open tensor steps and their composite, the normalized
displayed-coordinate compositor, Xi, and the six-object tensor-domain predicate.
Its `lean.declarations` lists the 29 corresponding existing declarations.
`finiteProductOrdinary` and its projection helper already have the landed owner
`def-pur-finite-ordinary-product`, which the item now cites separately.
No additional Lean file, theorem, or postponed proof is introduced.

Searches for this node: msearch LeanSearch and LeanFinder with
“Finite product compactification geometry and chosen forward tensor product map”
each returned eight generic tensor/topological-product results and no exact
match; the exact names are retained in `mathlib_searches`. The msearch Mathlib
grep `finiteProductGeometry|finiteProductChosenForward|FiniteProductCompactificationDomain`
returned zero hits. The same rg search in `lean/WeilConjectures`, `lean/Sheaf`
and `dag/nodes` found no upstream match or definition owner, and identified the
real published data in `FiniteProductCompactification`. The read-only
`blueprint_refs.py search 'finite product compactification data'` returned no
blueprint node; `ancestor` returned `prop-pur-affine-space-composition-law`.
The current blueprint Kunneth-coherence proof was reread, including the
compactification reduction and the composition/exchange/projection formula.
These search results are recorded verbatim by name/count, with the reuse verdict.

## Returned delivery repair

H2 against immutable head `929ccde60076` is repaired by registering the missing
definition owner and replacing the added theorem statement dependency with that
owner and `def-pur-finite-ordinary-product`. The current-main item differs only
in `stmt_deps` and `lean`; its statement and proof are retained. No dependency
record is rewritten. The retained Lean file is unchanged, SHA256
`9271b48d9cd56699af7414efff233a7913936fb700bb6c9c1e3521e589d0f0bf`.
The maintainer's mathematical approval applies to the same clause-by-clause
statement. Compilation, preflight, and delivery are rerun for this repaired packet.
