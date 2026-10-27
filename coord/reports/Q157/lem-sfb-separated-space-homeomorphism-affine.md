## Worker report

Item: lem-sfb-separated-space-homeomorphism-affine. The module
Sheaf.AlgebraicGeometry.SeparatedSpaceHomeomorphismIntegral states
AlgebraicGeometry.AlgebraicSpace.isRepresentableWith_isIntegralHom_of_separated_universally_isHomeomorph.
Its only theorem has proof `sorry`; no definition, auxiliary theorem, or new node is introduced.

Source read: David Rydh, Submersions and effective descent of étale morphisms,
https://davidrydh.se/papers/submersion20100305.pdf, Corollary (5.22), printed pp.24–25,
its proof, Appendix B opening paragraph, printed p.38, and the global quasi-separatedness
convention on printed p.4. The DAG proof explicitly supplies quasi-separatedness after
an affine test, so that global convention is not imposed as an extra hypothesis.

Hypothesis and clause correspondence:

- The base scheme S is `{S : Scheme.{u}}`; `u` is explicitly declared and unrestricted.
- Algebraic spaces X and Y over S are `{X Y : AlgebraicSpace S}`. The existing category
  is the full subcategory of fppf sheaves with representable diagonal and a surjective
  representable étale scheme atlas. No alternative space notion is introduced.
- The S-morphism is `(r : X ⟶ Y)`, a sheaf natural transformation on schemes over S.
- Separatedness is `(hsep : MapIsSeparated r)`. Its existing definition says that the
  canonical relative diagonal is `IsRepresentableWith` scheme closed immersions.
  This uses the recorded scheme closed-immersion notion, equivalently quotient by a
  quasi-coherent ideal, and does not assume that r itself is already representable.
- Universal homeomorphy is `hhome`: for every `(T : AlgebraicSpace S)` and `(t : T ⟶ Y)`,
  the canonical point map of the second projection of the sheaf pullback is an
  `IsHomeomorph`. The fibre product is an algebraic space by the recorded
  `fibreProduct_isAlgebraicSpace`; its existing Point topology is used unchanged.
  Neither an arbitrary point map nor an independently supplied homeomorphism is used.
- Representability and integrality together are the conclusion
  `IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) r.hom.hom`.
  Unfolding the recorded predicate quantifies over every `T : Over S` and every
  `a : yoneda.obj T ⟶ Y.obj.obj`, and supplies `U : Over S`, `p : U ⟶ T`, and
  `q : yoneda.obj U ⟶ X.obj.obj` with `IsPullback q (yoneda.map p) r.hom.hom a`
  and `IsIntegralHom p.left`. Thus U represents the actual base change X ×_Y T,
  with its specified projection, rather than an unrelated scheme.
- The explicit affine-open clause is contained in `IsIntegralHom`: it extends
  `IsAffineHom`, requiring affine inverse images of every affine target open,
  and its `isIntegral_app` requires the induced section ring homomorphism to be integral
  for every affine open. Hence these preimages are Spec B over Spec A with the specified
  A-algebra B. `RingHom.IsIntegral` means that every b is integral, and
  `RingHom.IsIntegralElem` means existence of a monic polynomial over A vanishing at b
  (Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean:38–47). There is no finite-type,
  finite-module, or reducedness requirement hidden in this predicate.

Dependency interfaces read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and Scheme.Hom;
  source signatures and docstrings at lines 36–46 and 73–75.
- def-trf-algebraic-space: Sheaf.AlgebraicGeometry.AlgebraicSpace,
  AlgebraicGeometry.AlgebraicSpace, AlgebraicSpace.IsAlgebraicSpace, and
  AlgebraicSpace.IsRepresentableWith; read the full file, especially the representing
  scheme and actual IsPullback witness in IsRepresentableWith.
- def-sfb-space-morphism-properties: Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties,
  AlgebraicSpace.MapIsSeparated, with the canonical `pullback.diagonal`.
- def-sfb-proper-curve-moduli: Sheaf.AlgebraicGeometry.ProperCurveModuli,
  AlgebraicSpace.mapPoint, the actual Quot.map on existing field-valued representatives.
- def-a1-space-point-topology: Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology,
  AlgebraicSpace.pointTopologicalSpace; it is the final topology for all representable
  étale scheme maps. Read also AlgebraicSpacePointClasses, Point and PointRepresentative.
- def-weil-finite-integral-morphism: Mathlib.AlgebraicGeometry.Morphisms.Integral,
  AlgebraicGeometry.IsIntegralHom (class and docstring at lines 32–37).

The latter four already-landed definition nodes are added to stmt_deps under the standing
permission for landed notions. No existing dependency interface is replaced, no new node
is created, and the natural-language statement and accepted proof are unchanged.
Statement imports are public. Existing proof-dependency modules are imported privately:
AlgebraicSpaceFibreProductsEtaleCovers (also reexported through the public property module),
SeparatedEtaleChart, SeparatedEtaleSpaceScheme, AlgebraicSpacePointOpenCalculus,
UniversallyHomeomorphIntegral, and the Mathlib integral/affine, closed-immersion, separated,
quasi-separated, relative-gluing and morphism-gluing APIs. The Mathlib Integral public
import supplies the affine, closed-immersion and separated modules transitively.
The other proof-dependency nodes currently have no Lean records and are not restated here.
The theorem docstring follows each of the five DAG proof steps and names their input nodes.

Edge cases checked before writing:

- Empty S, X, Y, and empty scheme tests are permitted; neither Nonempty nor a point is
  required. Universal homeomorphy forces an empty source whenever the target is empty.
- Identity maps of arbitrary algebraic spaces satisfy the hypotheses and the conclusion;
  the spaces need not be schemes themselves.
- Closed nil thickenings satisfy the intended condition; no reducedness is imposed.
- Purely inseparable field extensions and integral extensions not of finite type remain
  covered. No characteristic, Noetherian, finite-presentation or finite assumption occurs.
- A homeomorphism before base change alone does not suffice; the Lean hypothesis retains
  every algebraic-space base change, including the identity and arbitrary non-scheme T.
- Arbitrary non-quasi-separated bases and targets are retained. Quasi-separatedness in
  Rydh's argument is obtained locally over affine tests by the DAG proof, not assumed.
- All scheme tests, base schemes, and field representatives use the same explicit u as
  the existing algebraic-space framework; there is no smaller independent test universe.

Searches performed using msearch.py with group Q157 and this item:

- leanfinder: `A separated universal homeomorphism of algebraic spaces is representable
  by schemes and integral`. Eight hits: IsIntegralHom.of_comp and related scheme-only
  integral/separated properties. No exact algebraic-space theorem.
- loogle: `AlgebraicGeometry.IsIntegralHom, IsHomeomorph`. Zero hits.
- grep (AlgebraicGeometry): `AlgebraicSpace|universalHomeomorph.*integral|integral.*universalHomeomorph`.
  Zero hits in Mathlib. No algebraic-space result.
- leansearch: `Every separated universal homeomorphism of algebraic spaces is representable
  and integral`. Eight hits on scheme integral/universally closed morphisms, not this theorem.
- Direct rg in lean/WeilConjectures for the item id, AlgebraicSpace, and the universal
  homeomorphism/integrality patterns found no algebraic-space declaration or item binding.
- Direct rg in lean/Sheaf for separated/homeomorphism patterns and point/morphism property
  declarations found the recorded point topology, canonical mapPoint, and MapIsSeparated;
  the scheme-only UniversallyHomeomorphIntegral is a proof dependency, not an exact match.
  Further rg for the proposed theorem name in Mathlib, WeilConjectures and Sheaf found no
  collision. No duplicate statement was found.

Validation: scompile.py Q157 lem-sfb-separated-space-homeomorphism-affine compiled this
module in both sandbox and library modes, within the 60-second per-file limit, with
no errors or disallowed warnings. No statement dispute or source correction is needed.

## Second reading by Q157

This is the worker's separate second pass, not a claim of an independent agent review;
the dispatcher explicitly prohibits starting another agent, and the maintainer performs
independent review of the delivery. Reopened the node and module and checked S, X, Y,
r, separatedness and all algebraic-space base changes against their binders. Unfolded
IsRepresentableWith and IsIntegralHom in their source files to check the representing
pullback, affineness over every affine open, and the monic-polynomial condition.
The conclusion needs no redundant separate representability conjunct because the
scheme witness is part of IsRepresentableWith. Checked that the statement makes no
quasi-separatedness assumption or scheme-source restriction, that the point map is
canonical, and that autoImplicit is disabled. The only adjustment in this reading was
module-docstring whitespace. No mathematical mismatch was found. No new or repaired
dependency modules are present.
