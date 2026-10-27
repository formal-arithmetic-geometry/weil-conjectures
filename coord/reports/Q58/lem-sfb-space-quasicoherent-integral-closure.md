## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIntegralClosure`
states `AlgebraicGeometry.AlgebraicSpace.existsUnique_quasiCoherent_integralClosure`.
It has one named theorem with whole proof `sorry`, and no new definitions.
The source read was `literature/stacks-project/spaces-morphisms.tex`, Tag 0820,
`lemma-integral-closure`, lines 9718–9767: the statement constructs the quasi-coherent
subalgebra with the required affine values. The uniqueness follows by checking
membership on affine open covers, exactly as the DAG's final proof step explains.
The theorem docstring gives all six proof steps from the node.

Hypothesis and clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, using the recorded Mathlib scheme type.
- An algebraic space X over S: `(X : AlgebraicSpace S)`, the recorded fppf-sheaf
  full subcategory with representable diagonal and an étale surjective scheme atlas.
- The size convention: explicit `universe u`; `X.EtaleSite` has scheme-chart objects
  in universe u+1 and section rings in u, exactly the dependency's interface.
  No equality between the site object and section universes is imposed.
- A sheaf of commutative O_X-algebras on the small étale site:
  `(A : X.CommAlgebraSheaf)`, the already landed under-category of the commutative
  regular-functions sheaf. Its right object is a sheaf of commutative rings; its
  structure arrow is `A.hom`.
- Its underlying module is quasi-coherent: `(hA : A.toModule.IsQuasicoherent)`.
  `toModule` restricts the algebra's unit module along the actual structure map;
  `IsQuasicoherent` is Mathlib's predicate of site-local presentations.
- Existence and uniqueness of an O_X-subalgebra of A: `∃! C : Subobject A`.
  These are subobjects in the category of commutative algebra sheaves, so the
  inclusion preserves ring operations and the O_X structure map. Equality of
  subobjects means equality as embedded subalgebras, independent of a chosen carrier.
- The subalgebra is quasi-coherent:
  `(C : X.CommAlgebraSheaf).toModule.IsQuasicoherent`.
- Every affine scheme U étale over X: `∀ (U : X.EtaleSite),
  IsAffine (X.etaleForget.obj U) → ...`; étaleness is part of the site's objects.
- Its affine sections are exactly the integral elements: for every
  `a : A.right.obj.obj (op U)`, the displayed iff identifies membership in the image
  of `(Subobject.arrow C).right.hom.app (op U)` with
  `(A.hom.hom.app (op U)).hom.IsIntegralElem a`.
  Read in Mathlib's `IsIntegral/Defs.lean:39`, the latter is exactly existence
  of a monic polynomial over the domain ring with eval₂ along that ring map zero.
  The domain is Γ(U,O_U), by `commStructureSheaf`'s definition.
- The specified inclusion: the image is taken using `Subobject.arrow C` itself.
  A subobject arrow is a monomorphism, and its ring-sheaf map is an injective
  section map. Thus this characterizes the actual embedded subalgebra of A(U),
  including its inclusion, rather than an abstract algebra isomorphism.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh`, using `SheafOfModules.IsQuasicoherent` unchanged.
- `def-weil-size-convention` is explicitly recorded as a metatheoretic convention;
  there is no declaration to import.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`:
  `AlgebraicSpace.commStructureSheaf`, `CommAlgebraSheaf`,
  `CommAlgebraSheaf.toModule`, `QCAlg`. This already landed definition node
  `def-sfb-space-quasi-coherent-algebra` was added to `stmt_deps`, as permitted
  for already landed missing notions; its record is not changed.
- `Mathlib.CategoryTheory.Subobject.Basic`: `CategoryTheory.Subobject`,
  `Subobject.arrow` and its coercion, used for an embedded subalgebra with uniqueness.
- `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`: `RingHom.IsIntegralElem`.
  This avoids installing an arbitrary algebra structure and uses the given map.

The stated proof dependencies are imported without `public`:
`Mathlib.RingTheory.Smooth.IntegralClosure`
(`TensorProduct.toIntegralClosure_bijective_of_smooth`),
`Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`
(`Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`),
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`
(`AlgebraicSpace.representable_etale_scheme_tests`),
`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
(`Scheme.Modules.exists_tensorPullback_affine_sections`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
(`Scheme.Modules.isQuasicoherent_pullback`), and
`WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover`
(`Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover`).
The source signatures and proof docstrings were read. The two proof-only nodes
`lem-sfb-scheme-quasicoherent-integral-closure` and
`lem-sfb-space-qcoh-cartesian-chart-family` have no recorded Lean statement or
Mathlib match in the read repository; hence they supply no import yet. They
are not needed to type this statement. No missing statement dependency remains.

Edge cases checked: the empty algebraic space and empty affine chart require no
nonemptiness assumption (the zero ring is allowed). For A=O_X all elements satisfy
X-a, so the subalgebra is the whole structure sheaf. For a quotient algebra O_X/I
all local elements are scalar images and integral, again giving the whole algebra;
there is no injectivity requirement on the structure map. For k[t], the condition
selects elements integral over k, while nilpotents are correctly included (e.g.
k[ε]/(ε²)). Neither reducedness, normality, quasi-compactness, separatedness nor
finite type of X or A has been added. Uniqueness is among embedded subalgebras,
not among unlabelled isomorphic algebra sheaves.

Searches actually run using `msearch.py Q58 lem-sfb-space-quasicoherent-integral-closure`:

- leanfinder: “A quasi-coherent algebra on an algebraic space has a quasi-coherent
  integral closure subalgebra with affine sections the integral elements”. Eight
  hits concerned integral scheme morphisms and scheme normalization, no exact match.
- loogle: `integralClosure, SheafOfAlgebras, Subalgebra`. Zero hits; unknown
  identifier `SheafOfAlgebras`, so this query alone was inconclusive.
- grep: `integralClosure|integral_closure|SheafOfAlgebras|CommAlgebraSheaf`,
  Mathlib/AlgebraicGeometry. Five hits, all in scheme Normalization.lean;
  none states Tag 0820 for an algebraic space or an arbitrary algebra sheaf.
- leansearch: “integral closure of a quasi coherent sheaf of algebras on an
  algebraic space is quasi coherent”. Eight ring-level hits, including
  `integralClosure`, `integralClosure.isIntegral`, and `IsIntegralClosure`;
  no algebraic-space sheaf theorem.
- Local rg of `lean/WeilConjectures` and `lean/Sheaf` for algebra sheaves,
  subalgebras, integral closures, and the item id found scheme-only algebra
  modules and the already landed algebraic-space algebra interface above.
  Searches for the item id and proposed declaration in both library roots and
  `dag/lean_names_upstream.json` found no existing target declaration.
  Source inspection established that `CategoryTheory.commAlgebraSheafModule`
  is limited to the opens of a topological space, while the selected dependency
  is exactly the small étale algebraic-space interface needed here.

No statement correction, dispute, new node or dependency repair was needed.
Only `lean` and the addition of the landed algebra-definition statement dependency
are changed in the item node.

Validation: `scompile.py Q58 lem-sfb-space-quasicoherent-integral-closure <module>`
compiled the sandbox and library module names cleanly (2.2 s and 2.4 s respectively).
No diagnostic commands or auto-bound variables remain. Every source line is at
most 87 characters. The dry run and final delivery are run after this report.

## Second reading by Q58

The dispatcher expressly prohibits starting other agents; no independent worker
review is claimed here. A separate pass by the author re-opened the node and Lean
signature and checked every clause above against Tag 0820. In particular it checked
that Γ(U,O_U) is the actual domain of `A.hom` on U, that A's quasi-coherence is a
hypothesis and C's is a conclusion, that all affine étale objects are quantified,
and that `∃!` concerns a subobject with its fixed inclusion. The possible mismatch
between isomorphism of bare algebras and equality as embedded subalgebras is avoided
by `Subobject A` and by using its own arrow in the image condition. No mismatch
or further edit was found in this pass. The maintainer's independent review remains
the independent reading of this dispatcher delivery.
