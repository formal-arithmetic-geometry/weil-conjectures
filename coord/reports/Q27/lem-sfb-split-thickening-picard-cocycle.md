## Compile-time repair (continued returned delivery)

H2 remains repaired: stmt_deps cites the existing definition owner
`def-pc-module-cohomology-ext-resolution-equiv`, not its separate naturality theorem.
The earlier unchanged-file timeouts below are historical failed validations, not a
current reason to stop. A prefix probe containing only splitThickeningPicardClass
also timed out. Profiling showed costly conversion through the bundled composite.
The equivalent pointwise function passed server confirmation in 44.2 seconds;
adding @[no_expose] passed the library check in 22.1 seconds. The real construction
still applies exactly the module/Ext equivalence, H1(a ↦ 1+epsilon a), and inverse
Hilbert 90. No chosen equivalence or new hypothesis is introduced.

The helper splitThickeningPicardClass now has an ordinary function type instead of
an AddMonoidHom type; all existing uses apply it to a cohomology class, so the seven
mathematical theorem signatures are unchanged. The additive property is explicitly
stated by the existing beta AddEquiv and tensor theorem. The new public helper
splitThickeningPicardClass_apply gives the exact pointwise equation with proof sorry,
a source/proof docstring and an entry in lean.declarations. It characterizes the
non-exposed construction for downstream users. A search for all three helper names
in current lean/Sheaf and lean/WeilConjectures found no landed consumer; every use
in this packet is retained and compiled. No external user adaptation is required.

## Worker report

Final repair validation (2026-10-24): scompile.py passed the complete repaired
module with no warnings or errors (sandbox 27.9 s, library 38.6 s). The prescribed
dry run passed: `OK (dry run): commit 3f6049d4dad passes the preflight and compiles;
nothing pushed`. The dependency owner, exact recorded main signature, eight
sorry-only theorems (seven mathematical clauses plus the defining equation),
explicit universe binding and line width were checked again before delivery.

Repair of returned head 0a10ad30e418, H2 (2026-10-24): replaced the statement
dependency `new-module-cohomology-ext-resolution-naturality` with the existing,
reviewed definition node `def-pc-module-cohomology-ext-resolution-equiv`.
Read its statement and Lean record and the owning declaration at
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality:592`.
The consumer uses only `Modules.moduleCohomologyExtResolutionEquiv`, in the
canonical Picard class and tangent conclusion; it uses no conclusion of the
separate naturality theorem. The dependency paragraph below now cites the definition
owner. The Lean module, signatures, and all other node fields are unchanged.
The current main node was compared with the retained packet before repair; its
only differences were the previously delivered `lean` and `stmt_deps` fields.

Current saved-packet validation (2026-10-24): retained the statement module and node,
read both against the current source node, and confirmed the exact recorded signature,
explicit universe binding, 100-character line width, and seven sorry-only theorems.
The prescribed dry run passed: `OK (dry run): commit 732b64d1ffe passes the preflight
and compiles; nothing pushed`. Its local compile timed out, but the wrapper's
confirmation against current server sources succeeded. The earlier server-storage
failures below are historical; this attempt passed without changing the Lean packet.

The module `Sheaf.AlgebraicGeometry.SplitThickeningPicardCocycle` states every clause
of lem-sfb-split-thickening-picard-cocycle in seven mathematical theorems, all with proof `sorry`, plus a defining application lemma.
It adds three explicit helpers belonging to this same construction: the canonical
exponential cohomology map, projection to a Cech cocycle coefficient, and the
predicate expressing frames with its exponential transition functions. There are
no new independent notions, new DAG nodes, dependency repairs, or statement corrections.

Sources read: Stacks `more-morphisms.tex`, lemma-picard-group-first-order-thickening
(Tag 0C6R), including its units-sequence proof; `cohomology.tex`, lemma-h1-invertible
(Tag 09NU), including its frame torsor construction; Milne, Abelian Varieties,
Chapter III Proposition 2.1, printed pp.90–91 (PDF text extracted and read).
Milne explicitly uses a ↦ exp(a epsilon)=1+a epsilon. The current latest blueprint
unit's direct-images statement was also read; this item is an auxiliary lemma,
not that unit's own statement. The reviewed node proof has nine steps, and their
arguments are distributed among the seven theorem docstrings.

Hypotheses and clauses, checked against the Lean:

- Field and k-scheme: each theorem has `{k : Type u} [Field k]`, `X : Scheme.{u}`
  and `[X.Over (Spec (.of k))]`. The helpers are constructions on arbitrary schemes;
  the statements about the item have its field and structural-map hypotheses.
- A=k[epsilon]/epsilon squared: existing Mathlib `DualNumber k`, with `DualNumber.eps`.
  The existing `X.dualNumbers` is the same-space model of the base change in the
  node, with sections `DualNumber Γ(X,U)`. Its identification with the literal
  `pullback (X ↘ Spec k) (Scheme.dualNumbersOver (Spec k)).hom` is the existing
  `Scheme.isPullback_dualNumbersProj ... |>.isoPullback`. For Spec k, the existing
  `Scheme.dualNumbersToSpec` identifies this base with Spec (DualNumber k).
  Thus no extra choice of thickening, projection, or reduction is assumed.
- Projection p and inclusion j: `X.dualNumbersProj` and `X.dualNumbersι`.
  Their composition is the identity, as in the upstream construction.
- Picard group: the existing `Scheme.Pic`, its tensor group law and dual inverse,
  `Pic.map` for pullback and `Pic.mapHom ... |>.ker` for the actual reduction kernel.
  `Additive` changes notation on this existing multiplicative abelian group.
- H1 means module cohomology: the source and argument types of the canonical map
  and the six scheme theorems are literally
  `(RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X)`.
  The definition composes the existing constructed
  `Modules.moduleCohomologyExtResolutionEquiv X (Modules.unit X) 1`,
  `Sheaf.H.map X.dualNumbersOneAddEps 1`, and the inverse Hilbert-90 additive
  equivalence `Pic.toH1UnitsDualNumbersAddEquiv X`. It does not choose an arbitrary
  equivalence from a Nonempty theorem. The first comparison is built from common
  injective-resolution section complexes and the terminal-source identification.
- Canonical beta: `splitThickeningPicardCocycle` asserts an additive equivalence
  onto the actual kernel, whose underlying Picard value is exactly the defined
  `splitThickeningPicardClass`. Thus its existential equivalence is uniquely fixed
  by an explicit map; it cannot be replaced by an arbitrary abstract isomorphism.
- Any open covering: `_frames` has `I : Type u`, `U : I → X.Opens`, `hU : iSup U = ⊤`.
  There is no separatedness, quasi-compactness, affine-cover, or acyclicity hypothesis.
- Additive Cech cocycle: `z` is a degree-one cycle of the existing module-valued
  `CategoryTheory.cechComplexFunctor U` on `(Modules.unit X).presheafModuleCat`.
  `splitThickeningCocycleCoefficient U z y` is its component on the pair indexed
  by `y : Fin 2 → I`, using the existing product projection and cycle inclusion.
  The pair intersection is the categorical product of opens, as in that complex.
- Image in sheaf cohomology: `c` is a morphism from this Cech homology to module H1,
  and `hc : Modules.IsModuleCechComparison U (Modules.unit X) 1 c` fixes it to the
  canonical augmented-double-complex map. This is a specification of the existing
  comparison, not an assumption that the cover computes all cohomology.
- Gluing by 1+epsilon c_ij: `HasSplitThickeningFrames U z M` gives frames `s i`,
  the recorded `Modules.IsFreeGenerator` condition for every frame, and exactly
  `s_j| = (1+inr(c_ij)) s_i|` on each pair intersection. `M.smul ... |>.hom`
  explicitly applies the section module's scalar multiplication. `_frames` asserts
  existence of an invertible M with these frames and identifies the class of every
  invertible M with these frames with beta of `c (homologyπ 1 z)`.
- Deformation of L: `_deformation` binds invertible `L : X.Modules` and
  `M : X.dualNumbers.Modules`, and explicitly assumes
  `hred : Pic.map X.dualNumbersι (Pic.ofIsInvertible M) = Pic.ofIsInvertible L`.
  The units `t y`, generators `s i` of L and `r i` of M, and equations `ht`, `htr`
  are precisely the transitions t_ij and t_ij(1+epsilon c_ij). Its conclusion is
  `[M] * (Pic.map p [L])⁻¹ = beta([c])`, the class of M tensor p-star L inverse.
- Pullback naturality: `_pullback` takes arbitrary k-schemes X,Y and `f : Y ⟶ X`,
  with `hf` saying f commutes with the structure maps. The thickening morphism is
  the existing `f.dualNumbers`. The cohomology map is the existing
  `Modules.moduleCohomologyFMap f (SheafOfModules.unitToPushforwardObjUnit ...) 1`,
  i.e. the canonical h-map f sharp from O_X to f-star O_Y. It is the usual pullback
  composed with the canonical map f-star O_X to O_Y, not a newly selected map.
- Scalar naturality: `_scale` binds every `a : k`. The scheme endomorphism is
  `X.dualNumbersScale (globalSectionsRingHom k (X := X) a)` and the scalar on
  right-derived module H1 is the same global section. Restriction along this
  structure ring map is exactly scalar multiplication by a in its k-vector space.
  There is no nonzero or unit hypothesis; zero is included.
- Tensor/addition: `_tensor` states explicitly that the value at v+w is the product
  of the two Picard values. The main beta is also an AddEquiv. The helper is a pointwise function;
  the tensor theorem and beta equivalence specify its additive property.
- Tangent hypotheses: `_tangent` adds `[IsSepClosed k]`,
  `[SmoothOfRelativeDimension 1 ...]`, `[IsHProjective ...]`,
  `[GeometricallyIntegral ...]`, and a k-point `p` with the structure-section
  equality `hp`. These are the smooth projective geometrically integral curve
  and rational-point hypotheses of the node. No connectedness or properness
  assumption is added: they follow from the recorded geometric/projective classes.
- Represented Picard: `_tangent` uses the full `picardFunctor`, not a substitute
  functor: `e : (picardFunctor ...).obj.RepresentableBy J`, `[GrpObj J]` and the
  existing `IsPicardMul ... e` specify a representation as a group functor.
  This is the induced tensor group law implicit in 'represented Picard functor'.
  It is not a restriction of representability: the upstream
  `exists_commGrpObj_isPicardMul` supplies precisely this structure for every e.
- Tangent normalization: `tangentSpaceAt J η[J]` is the existing dual-number tangent
  space. The conclusion gives `Φ : tangentSpaceAt J η[J] ≃ₗ[k] (Modules.unit X).H 1`
  and, for every tangent vector and every line bundle representing it through e,
  requires its class on the same-space thickening to equal beta of the module-H1
  class corresponding to Φ(v). This is equivalent to Φ(beta(w))=w. The existing
  constructed module/Ext equivalence explicitly transports the H1 model, so the
  tangent convention in lem-sc-pic-tangent-space is retained. Although that node's
  existing theorem only states Nonempty for Pic0, our stronger normalization is
  an additional clause of this item, not a redefinition of its tangent notion.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.AlgebraicGeometry.Scheme: `Scheme`,
  `Scheme.Hom`; Mathlib.Algebra.DualNumber: `DualNumber`, `DualNumber.eps`.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions:
  `Scheme.Modules.moduleBaseChange` and its underlying pullback conventions.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `Scheme.Modules.IsInvertible` (the scheme-level notion throughout).
- WeilConjectures.AlgebraicGeometry.PQFCohomology:
  `sheafCohomologyAndHigherDirectImages` and its literal
  `RingedSpace.moduleCohomology` convention.
- WeilConjectures.AlgebraicGeometry.Picard.Jacobian:
  `picardFunctorDegree`, `nonempty_tangentSpaceAt_linearEquiv_H_one`,
  `tangentSpaceAt` and its existing vector-space structure.
- WeilConjectures.AlgebraicGeometry.Picard.Defs: `picardFunctor`, `toPicardFunctor`;
  Picard.Group: `IsPicardMul`, `Pic.ofIsInvertible`, `Pic.mapHom`.
- WeilConjectures.AlgebraicGeometry.DualNumbers: the thickening, inclusion,
  projection, scaling, morphism and canonical pullback square described above.
- WeilConjectures.AlgebraicGeometry.Picard.DualNumbers:
  `dualNumbersOneAddEps`, `Pic.toH1UnitsDualNumbersAddEquiv`.
  `exists_addEquiv_ker_picMap_dualNumbersι` is a partial match only: it omits the
  transition formula, arbitrary pullback, and represented tangent normalization.
- Existing nodes added to stmt_deps (all already have usable recorded Lean):
  def-sc-module-cech-comparison (`ModuleCechComparison.IsModuleCechComparison`);
  def-pc-module-cohomology-ext-resolution-equiv
  (`ModuleCohomologyExtResolutionNaturality.moduleCohomologyExtResolutionEquiv`);
  def-weil-pbc-module-cohomology-fmap (`ModuleCohomologyFMap.moduleCohomologyFMap`);
  def-sc-picard-group (`PicardFunctor.Scheme.Pic`);
  def-sc-local-free-generator (`Modules.FreeGenerator.Modules.IsFreeGenerator`).
  Module prefixes in this paragraph abbreviate WeilConjectures.AlgebraicGeometry;
  declaration namespaces are as written explicitly above. These are references to
  landed existing notions; no copied definition or dependency module was needed.

Proof-only imports include the recorded right-derived universal delta-functor,
Picard-H1 restriction compatibility, module/abelian Zariski comparison, torsor-H1
functoriality, Cech comparison systems/existence/inverse-image-unit and scheme tangent
space. Hilbert 90, torsors, and the Picard splitting are already exposed by the
imported upstream Picard modules. No import is added to an upstream file.

Edge cases checked mathematically before writing: empty X and the empty cover;
a one-member cover (all represented H1 classes are zero); Spec k and P1 (zero
H1 and trivial reduction kernel); a positive-genus smooth projective curve
(nontrivial first-order line bundles); characteristic 2; v=0; zero scaling;
identity and arbitrary k-morphisms; nonseparated and non-quasi-compact X in the
general statements. No finite-cover, dimension, or nonemptiness restriction is
silently imposed outside the curve clause. The cover index universe is u, the
scheme's point/open universe, following the existing Cech API; every open covering
can be indexed by its set of opens with repetitions removed. All universes and
variables are explicitly bound; autoImplicit is false.

Searches actually run with the prescribed msearch.py:

- leanfinder: `Picard group kernel split dual number thickening H1 structure sheaf
  transition cocycle one plus epsilon` — eight hits, cotangent objects and ring
  relative Picard groups; no scheme-level statement matching all clauses.
- loogle: `Scheme.Pic, DualNumber, CechCocycle` — zero hits; the service reported
  unknown identifier Scheme.Pic, so this is not evidence of absence by itself.
- grep: `Picard|dualNumbersOneAddEps|CechCocycle` in Mathlib AlgebraicGeometry —
  three elliptic-Weierstrass comments about Picard groups, no matching construction.
- leansearch: `Picard group infinitesimal line bundle split square zero thickening
  cohomology` — eight hits, including CommRing.Pic and local-ring triviality,
  but none is the scheme cohomology/cocycle/tangent theorem.
- rg throughout lean/WeilConjectures and lean/Sheaf, and the upstream-name index,
  for the node ID and each proposed declaration name — no existing declaration.
  Concept searches found the upstream Picard.DualNumbers partial theorem and the
  downstream AbelDifferentialBoundary consumer. Those were opened and read;
  the former is reused, and its omitted clauses prevent an existing:true binding.

No STATEMENT-DISPUTED or node fault was found. The full Picard representation and
canonical module cohomology are retained rather than silently specialized.

Validation: prescribed scompile.py runs found and repaired section scalar-application
inference, explicit scheme selection for the scalar structure map, and one long line.
The wrapper's local scratch-device-full condition automatically fell back to server
compilation. Final clean compilation and delivery preflight are recorded below.

Final verification: scompile.py completed with exit 0 and no Lean warnings or errors
(server compile, 32.3 seconds). deliver2.py --no-push printed
`OK (dry run): commit 5247da1ba3a passes the preflight and compiles; nothing pushed`.

Delivery tool failure: the normal delivery passed compilation/preflight and built
commit 921e31ff015c04d06c6dda1f82107043407f77ac, but its push was rejected with
`remote unpack failed: unable to create temporary object directory`.
A second prescribed deliver2.py invocation failed during compilation with
`resource exhausted (error code: 28, no space left on device)`.
No tools or shared repository files were modified. The complete validated packet
remains in this sandbox; no DELIVERED push acknowledgment was received.

Retry on 2026-10-24: inspected the saved packet and ran the prescribed
`deliver2.py Q27 lem-sfb-split-thickening-picard-cocycle --no-push` twice.
Both attempts failed during server compilation of `Sheaf.Stage2.Sandbox0` with
`resource exhausted (error code: 28, no space left on device)` after 26.6 seconds.
No Lean diagnostic was produced and nothing was pushed. The Lean module and node
record were retained unchanged; server storage remains the tool blocker.

Further retry on 2026-10-24: inspected this saved report and retained module, then
ran the prescribed `deliver2.py Q27 lem-sfb-split-thickening-picard-cocycle --no-push`
twice. Both returned exit 1 during server compilation of `Sheaf.Stage2.Sandbox0`:
`resource exhausted (error code: 28, no space left on device)` after 26.6 seconds.
There were no Lean diagnostics to repair. Nothing was pushed, and the module and
node record remain unchanged. This is the same server-storage tool failure as in
the preceding attempts; no launcher scripts or shared repository files were edited.

Dispatcher retry on 2026-10-24 (current worker): read the retained report and module,
checked the packet against the current source node (only lean and the documented
stmt_deps additions differ; statement unchanged; no released repair note), and ran
`deliver2.py Q27 lem-sfb-split-thickening-picard-cocycle --no-push` twice.
Both invocations returned exit 1 during server compilation of
`Sheaf.Stage2.Sandbox0`, reporting
`resource exhausted (error code: 28, no space left on device)` after 26.6 seconds.
No Lean diagnostic was produced. No push was attempted, and the module and node
were retained unchanged. The required compile/preflight cannot complete until the
server storage failure is repaired; no launcher script or shared file was edited.

Final dispatcher retry on 2026-10-24: inspected the saved report and Lean module,
checked the packet against the current source node (only `lean` and the five
previously documented `stmt_deps` additions differ; the statement is unchanged;
no repair note is present), and ran the prescribed
`deliver2.py Q27 lem-sfb-split-thickening-picard-cocycle --no-push` twice.
Both invocations exited 1 during server compilation of `Sheaf.Stage2.Sandbox0`
with `resource exhausted (error code: 28, no space left on device)` after 26.6 s.
There were no Lean diagnostics to repair. Neither invocation pushed anything.
The saved module and node remain unchanged; no launcher script or shared
repository file was edited. Server storage still prevents compile/preflight.

Saved-packet retry on 2026-10-24: inspected the retained report, module and
current source node; the statement is unchanged, only lean and the five documented
stmt_deps additions differ, and no repair note exists. Ran the prescribed
`deliver2.py Q27 lem-sfb-split-thickening-picard-cocycle --no-push` twice.
Both exited 1 during server compilation of `Sheaf.Stage2.Sandbox0` with
`resource exhausted (error code: 28, no space left on device)` after 26.6 s.
There are no Lean diagnostics to repair. Nothing was pushed. The module and node
remain unchanged; server storage prevents the required compile/preflight.

Current saved-packet retry on 2026-10-24: inspected report.md and the retained Lean
module, compared the node to the current read-only source, and checked for a repair
note (none present). The statement is unchanged; only lean and the five documented
stmt_deps additions differ. Ran the prescribed deliver2.py --no-push twice. Both
exited 1 during server compilation of Sheaf.Stage2.Sandbox0 with
`resource exhausted (error code: 28, no space left on device)` after 26.6 seconds.
Neither produced a Lean diagnostic or pushed anything. The module and node remain
unchanged. Required compilation/preflight is blocked by server storage; no launcher
script or shared repository file was edited.

Saved-packet dry-run retry on 2026-10-24: inspected the retained report and module,
compared the sandbox node to the current source (statement unchanged; only lean
and the documented stmt_deps additions differ), and checked for a repair note
(none present). Ran the prescribed deliver2.py --no-push twice. Both failed during
server compilation of Sheaf.Stage2.Sandbox0 with `resource exhausted (error code:
28, no space left on device)` after 26.6 seconds. No Lean diagnostics were
produced and nothing was pushed. The module and node remain unchanged; the server
storage tool failure prevents the required compilation/preflight.

Saved-packet retry (2026-10-24 10:56 UTC): inspected the retained report and Lean module,
compared the sandbox node with the current read-only node (only lean and the five
previously documented stmt_deps additions differ; statement unchanged), and checked
coord/returns/Q27.md for an item return (none found). Ran the required
`deliver2.py Q27 lem-sfb-split-thickening-picard-cocycle --no-push` twice.
Both exited 1 during server compilation of `Sheaf.Stage2.Sandbox0`, with
`resource exhausted (error code: 28, no space left on device)` after 26.6 seconds.
There were no Lean diagnostics to repair. Nothing was pushed. The Lean module
and node record remain unchanged; required compilation/preflight is prevented
by the server-storage tool failure. No launcher scripts or shared files were edited.

Returned-delivery H2 repair validation (2026-10-24): the requested dependency-owner
replacement and report paragraph correction are retained. The Lean module SHA256
remains 9a1eba77751dc8363323f3bf6e69909739d27514739a84629ada734e241621c6,
identical to returned head 0a10ad30e418. The prescribed scompile.py invocation and
two deliver2.py --no-push invocations all failed during compilation. Each reported
`SERVER CONFIRMATION` followed by
`Sheaf/AlgebraicGeometry/SplitThickeningPicardCocycle.lean: timeout after 60 s`.
There was no Lean type diagnostic. The second dry run was retried after an interval;
the timeout persisted. No compiler limit, launcher script, shared source, or Lean
module was changed. The repaired node/report remain saved; nothing was pushed.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
