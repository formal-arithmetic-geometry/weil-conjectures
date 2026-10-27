## Worker report

The module states `AlgebraicGeometry.AlgebraicSpace.exists_finiteDegree_ideal_blowupPresentation`
with one `sorry`, and defines nothing. The node statement, proof and source are unchanged.
Its statement dependencies gain five already landed definition nodes used by this interface;
there are no new nodes or dependency modules. Every variable is explicitly bound, with
`set_option autoImplicit false` and an explicit universe `u`.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `T : AlgebraicSpace S` uses the existing
  fppf-sheaf definition and its small etale structure sheaf. The same `u` in these
  interfaces is their existing universe convention, with site objects in `u+1` and
  sections in `u`. No equality of independent universes is imposed.
- Quasi-compactness, exactly as specified in the node, is `hqc`: an `Over S` scheme
  `V` with `CompactSpace V.left` and a representable etale surjective `a` to `T`.
- Quasi-separatedness is `hqs : IsAbsolutelyQuasiSeparated T`, the recorded
  absolute-diagonal affine-test criterion (Stacks 0AHR), valid over any base `S`.
- The finite-type quasi-coherent centre is `I : QuasiCoherentIdeal T` and
  `hI : (I.val : T.Modules).IsFiniteType`. Quasi-coherence is part of the subtype.
- `B : BlowupPresentation I` supplies the first blowup `B.space` and projection
  `B.projection`. This is the existing presentation requiring every affine etale
  base change to be the ordinary scheme blowup, hence exactly the descended Rees
  Proj specified in the node. It is not an arbitrary space or morphism.
- The upstairs ideal is `J : QuasiCoherentIdeal B.space` and its finite-type
  condition is `hJ : (J.val : B.space.Modules).IsFiniteType`.
- The positive integer is `d : ℕ` with `0 < d`, equivalently an integer d > 0.
  `H : QuasiCoherentIdeal T` and `(H.val : T.Modules).IsFiniteType` give the
  required finite-type quasi-coherent ideal downstairs.
- `H ⊆ I^d` is the inclusion, on every small etale test `V`, of
  `Set.range (H.val.arrow.val.app (op V))` in
  `idealPowerSubsheafSections I.val.arrow (SheafOfModules.unit T.structureSheaf)
  (fun _ ↦ Set.univ) d V`. This uses the existing sheafified product, not the
  potentially smaller power of global sections.
- The extended ideal `im(p^* H -> O)` is `image.ι (idealTensorMap B.projection H)`.
  Its range on every test is equated to `idealPowerSubsheafSections` applied to
  `image.ι (idealTensorMap B.projection I)` and the section family of `J`.
  This is precisely `E^d J`. Categorical image is essential: the image of a map
  of sheaves can be larger on nonaffine sections than the sectionwise image of
  the original map. Equality of the two section families on every test is exactly
  equality as ideal subsheaves, with no choice of inclusion representatives.
- No reducedness, density, nonemptiness, Noetherianity or regularity hypothesis is
  present. Open/closed immersion and morphism conventions are the existing
  project and Mathlib interfaces imported through the recorded dependencies;
  they do not add hypotheses to this ideal identity.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, `EtaleSite`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  slice instances exposing Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`: `QuasiCoherentIdeal`
  and `idealTensorMap`, the canonical adjoint of inclusion followed by the
  structure map; no second ideal or pullback definition is introduced.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation`: `BlowupPresentation`
  and `blowupChartIdeal`; these use
  `WeilConjectures.Blowup.Gluing`'s `Scheme.IdealSheafData.blowup` and `blowupMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees`:
  `idealSectionImage` and `idealPowerSubsheafSections`, owned by the landed node
  `def-sfb-space-ideal-power-products`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf`:
  `etaleAlgebraModulesHasSheafify`, `etaleAlgebraModulesWEqualsLocallyBijective`;
  with `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` these expose the
  standard Abelian instance and categorical images, without an extra hypothesis.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsSeparated`, `MapIsFiniteType`, `MapIsProper`; open and closed scheme
  immersions are Mathlib's `IsOpenImmersion` and `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleTensorAdjunction`, `moduleTensorSection`.

All currently recorded proof-dependency modules are imported with plain `import`.
Three proof dependencies currently have no Lean record: qcoh-kernels-colimits,
blowup-chart-properties and proj-finite-degree-equations. They are not needed to type this statement.
The complete five-step proof is retained in the theorem docstring, including the
homogeneous-localization kernel calculation and the no-cancellation argument.

Edge cases checked before writing and rechecked against the final signature:
empty T and empty blowup, I=0, nilpotent I, I=O_T, J=0, J=O, zero chart rings,
empty standard opens and zero-divisor chart denominators. The theorem permits
all these cases; H=0 handles an empty blowup, I=O gives the identity blowup and
H=J, and J=0 admits H=0. Positive d is required; no division or cancellation is
encoded. The product predicate sheafifies locally and includes empty covers.
Absolute quasi-separatedness does not assume the base scheme is quasi-separated.

Searches performed:

- `msearch.py ... leanfinder`: "Every finite type quasi coherent ideal on the
  blowup of an ideal on a qcqs algebraic space descends after multiplication by
  a positive power of the exceptional ideal"; eight hits about scheme section
  extension and ideal operations, no algebraic-space blowup identity.
- `msearch.py ... leansearch`: "A finite type ideal on an algebraic space blowup
  descends after twisting by the exceptional ideal"; eight hits about scheme
  descent, ordinary ideal operations and finite type algebras, no match.
- `msearch.py ... loogle '"blowup", "Ideal"'`: zero hits.
- `msearch.py ... grep 'blowup.*ideal|ideal.*blowup' AlgebraicGeometry`: zero hits.
- `rg` over `lean/WeilConjectures/Blowup` for finite-degree and exceptional-ideal
  terms found `Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup` in
  `WeilConjectures.Blowup.FiniteDegree.Main`. Its complete signature was read:
  it is scheme-only and does not quantify over algebraic spaces.
- `rg` for the item id in `lean/WeilConjectures`: no attachment.
- `rg` over `lean/Sheaf/AlgebraicGeometry` for blowup/ideal/finite-degree notions
  found the existing ideal, blowup, product and absolute-quasi-separated interfaces
  listed above, and downstream composition consumers, but no theorem with this
  statement. DAG records for all those definitions were read before reuse.
- Read the local Stacks `spaces-divisors.tex` Tag 0860 proof and Tag 085M.
  The source's displayed identity says X'' in the following prose, but its
  actual maps and final chart calculation live on X'; the node already corrects
  this typo. No statement correction is necessary.

Validation: `scompile.py` compiled both sandbox and library-module paths cleanly
(2.5 and 2.0 seconds). The first probe's missing `HasImage` instance was repaired
by publicly importing the existing full-site sheafification and Abelian interfaces.
There is no unresolved statement dispute.

## Second reading by Q85

Direct-delivery self-check, performed with the final node and final Lean module open;
no independent worker was started, as the dispatch brief prohibits other agents.
The binders match base scheme, space, qc atlas, absolute qs, finite-type centre,
its blowup, and finite-type upstairs ideal. The nested existentials match positive d
and finite-type H. The first universal section inclusion renders H contained in I^d;
the second universal section equality renders precisely im(p^*H)=E^d J on the first
blowup. Using categorical image inclusions avoids the nonaffine section-image error;
using `idealPowerSubsheafSections` avoids replacing a sheaf product by a global
section product. No assumptions were added to obtain images: the existing
sheafification instances suffice. No mismatch remains. No new definition, dependency
repair, source correction or change to a unit statement was made.
