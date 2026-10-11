## Worker report

The module states `AlgebraicGeometry.smooth_proper_diagonal_tensor_formula`, with one
sorry and no definitions. It specializes Stacks Tag 0A9U to a proper perfect closed
immersion, using the same explicit projection comparison encoding as the landed
`SmoothProperTensorPerfectCase` module. The source was read at
https://stacks.math.columbia.edu/tag/0A9U because the local Stacks TeX is absent.

Hypotheses and clauses:
- Noetherian schemes Z and Y are `{Z Y : Scheme.{u}} [IsNoetherian Z]
  [IsNoetherian Y]`. These include quasi-compactness and local Noetherianity.
- The closed immersion i is `(i : Z ⟶ Y) [IsClosedImmersion i]`; properness is
  `[IsProper i]`, retained although closed immersions are proper.
- Perfection of i_*O_Z over Y is `hperfect : Y.IsPerfect
  ((schemeDerivedDirectImage i).obj (𝟙_ (schemeDerivedCategory Z)))`.
  For a closed immersion, pushforward on modules is exact; thus this is precisely
  the degree-zero direct image in the node. It is locally perfect, not a global
  finite-free condition. The per-open HasDerivedCategory binder is required by
  the recorded definition of IsPerfect.
- The right adjoint c is quantified on the full quasi-coherent derived categories,
  with `adj` identifying it as right adjoint of the ObjectProperty lift of Ri_*.
  `hRf` merely witnesses the restriction; it is a conclusion, not a hypothesis.
- K is any `schemeDerivedQCohCategory Y`, without boundedness or perfection.
- O_Y is the derived tensor unit, lifted to the full subcategory with the
  existential quasi-coherence proof hO. The source tensor has underlying object
  `(derivedPullback i).obj K.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj`.
  hTensor witnesses membership in D_QCoh; again it is a conclusion.
- The canonical projection morphism is `pf.hom`, where `pf.inv` is pinned by
  the pullback adjunction `a.homEquiv`, the inverse monoidal comparison μIso,
  and the pullback counit. The composite with the c-adjunction counit at O_Y
  and the right unitor is the morphism Ri_*(Li^*K tensor c(O_Y)) -> K.
- `IsIso ((adj.homEquiv ... K) (ObjectProperty.homMk (...)))` asserts that
  precisely its mate is invertible. Its inverse gives c(K) ≅ Li^*K tensor c(O_Y).
  All choices of monoidal presentation and pullback adjunction are quantified;
  their existence is included as bookkeeping, exactly as in the landed sibling.

Declarations used:
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and its category.
- Mathlib.AlgebraicGeometry.Noetherian: IsNoetherian.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper.
- Sheaf.AlgebraicGeometry.DerivedCategory: schemeDerivedCategory,
  schemeDerivedQCohCategory, schemeDerivedQCohProperty.
- Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage: schemeDerivedDirectImage.
- Sheaf.AlgebraicGeometry.PerfectComplex: Scheme.IsPerfect.
- Sheaf.AlgebraicGeometry.DerivedPullback: derivedPullback, built from the recorded
  Scheme.Modules.tensorPullback in Sheaf.AlgebraicGeometry.TensorPullback.
- Sheaf.AlgebraicGeometry.DerivedTensorStructure: schemeDerivedTensorMonoidal.
- Mathlib CategoryTheory adjunction, full-subcategory lift/homMk, and monoidal
  morphisms and unitors render the mate without an unconstrained comparison map.
The ideal-sheaf dependency supplies no object used in this statement; its recorded
Scheme.Hom.ker remains unchanged. The right-adjoint dependency was read and supplies
existence for the proof; c is an arbitrary specified right adjoint, not its chosen one.
The two landed definition nodes for derived pullback and derived tensor structure
are added to stmt_deps; no new notions or dependency modules are introduced.

Edge cases: empty schemes, the identity immersion, zero K, and unbounded K are all
allowed. No nonemptiness, boundedness, positive dimension, or characteristic
hypothesis is imposed. A single explicit derived localization universe w matches
that of the recorded derivedPullback; all variables are explicit and autoImplicit
is disabled. The hperfect hypothesis is substantive (non-perfect quotient rings
are excluded), not a tautological property of an identity map.

Searches:
- msearch.py leanfinder: "right adjoint of proper perfect closed immersion derived
  pullback tensor dualizing complex" returned eight ordinary module/sheaf
  pullback-pushforward adjunction declarations, not this derived exceptional formula.
- msearch.py loogle: "Adjunction.homEquiv, IsIso" returned zero hits, reporting
  Adjunction.homEquiv as an unknown identifier; not counted as a matching declaration.
- msearch.py grep: "projection formula|perfect proper", AlgebraicGeometry,
  returned zero Mathlib hits.
- rg of WeilConjectures and lean/Sheaf for derived tensor, right adjoint, projection,
  and the item id: found the shared derived operations and the perfect-K sibling
  SmoothProperTensorPerfectCase, but no arbitrary-K immersion formula.
- rg of DAG records confirmed the derived pullback and monoidal tensor notions
  already have landed definition nodes. No second definition is needed.

Server compile: clean, 3.2 seconds; no errors or warnings.
No statement correction or STATEMENT-DISPUTED is needed.

## Earlier second reading (a previous round; superseded)

Pending: the dispatcher’s independent second reader must read the node, this module,
and its dependency signatures and replace this paragraph with the actual reading
before delivery. The author has not supplied an independent review.

## Second reading by S1

I independently reread the node statement, its Stacks source (duality.tex, Tag 0A9U),
all recorded statement dependencies, and the Lean declaration.

- Objects: Lean introduces Noetherian schemes `Z Y : Scheme.{u}`, a morphism
  `i : Z ⟶ Y`, closed-immersion and proper instances, the derived-category instances
  on `Z`, `Y`, and opens of `Y`, and the perfectness hypothesis
  `hperfect : Y.IsPerfect ((schemeDerivedDirectImage i).obj (𝟙_ (schemeDerivedCategory Z)))`.
  These render the node's proper perfect closed immersion and its local-perfect
  `i_* O_Z` hypothesis.  The existential witnesses `hRf`, `hO`, and `hTensor` are
  bookkeeping for quasi-coherence and tensor closure, as required by the recorded
  derived-category encoding; they are conclusions, not extra geometric hypotheses.
- Right adjoint and test object: after witnesses, Lean quantifies every monoidal
  structure on `derivedPullback i`, every adjunction
  `derivedPullback i ⊣ schemeDerivedDirectImage i`, every right-adjoint functor `c`
  with `adj`, and every `K : schemeDerivedQCohCategory Y`.  Thus the source's arbitrary
  right adjoint `c` and arbitrary quasi-coherent complex `K` are represented with the
  same quantifier order.
- Comparison: `pf` has source
  `Ri_* (Li^* K ⊗ c(O_Y))` and target `K ⊗ Ri_* c(O_Y)`; its inverse is pinned by
  `a.homEquiv`, the inverse monoidal comparison, and the pullback counit.  The final
  `IsIso` is the mate of `pf.hom` followed by the right-adjoint counit and right unitor,
  exactly the canonical comparison `Li^*K ⊗ c(O_Y) → c(K)`.  The displayed inverse
  orientation therefore gives the node's equivalent `c(K) ≅ Li^*K ⊗ c(O_Y)`.

No mismatch was found and no Lean or node repair was needed.  Edge cases checked are
empty schemes, the identity immersion, zero or unbounded `K`, and arbitrary `u,w`;
none is excluded, and there is no characteristic, nonemptiness, boundedness, or
positive-dimension assumption.  The empty-index issue does not arise (no indexed
family occurs).  The existing searches (LeanFinder/Loogle/grep and repository/DAG
searches recorded in the worker report) found no competing declaration or definition;
`SmoothProperTensorPerfectCase` is a distinct perfect-`K` statement.  The dependency
`def-sbc-closed-immersion-ideal-sheaf` is cited by the node but contributes no term to
this encoding, so it remains unchanged.  The module compiles cleanly with
`scompile.py`; its only proof placeholder is the permitted theorem `sorry`.
