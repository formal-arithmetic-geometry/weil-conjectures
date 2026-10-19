## Worker report

The interrupted sandbox retained only dispatcher marker files. No Lean module, node
copy, worker report, or second-reading section existed to preserve. This report and
the delivery files were reconstructed during the resumed second reading. The shared
node and its previously reviewed stage-1 correction are unchanged; only its `lean`
record is added. There are no new nodes, dependency repairs, theorem declarations,
proofs, or new sorries.

The module defines `WeilConjectures.TraceFormulaCoefficientSetup`. It is the type of
actual compactification families satisfying the prescribed geometric stability
requirements. It reuses all constituent notions; the preliminary conventions are
spelled out in the module documentation instead of making duplicate definitions.
Its signature parameters are the global finite-field datum, the distinct prime,
the finite extension, and the positive coefficient level. Its subtype property is
triangulatedness and repleteness, pullback preservation, and preservation by the
actual chosen-compactification composite. See the detailed object-by-object mapping
in the second reading below.

Dependencies opened and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (including its
  prime, positive exponent, cardinality, base field and algebraic-closure fields).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, reexporting
  `CoefficientExtension`: `Padic.coefficientExtensionRing`,
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`,
  and `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Scheme`, `Over`, `Morphisms.Proper`,
  `Morphisms.FiniteType`, `Morphisms.QuasiCompact`: `Scheme`, `Spec`, `Over`,
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and `IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `X.nilradical.subscheme`;
  `Mathlib.CategoryTheory.MorphismProperty.Limits`: `universally`, combined with
  `topologically IsHomeomorph` for the universal homeomorphism convention.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `Scheme.HasFiniteProEtaleTorAmplitude`, with one ordered integer interval for
  all degree-zero module sheaves.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`, exactly
  the conjunction of the preceding two predicates, also available on arbitrary
  schemes. The currently recorded `FiniteTorAmplitudeProEtaleModule` reexports
  that unchanged intrinsic definition and transports it to fixed-scalar sheaves;
  this delivery directly uses the intrinsic definition, so needs no transport.
- `Mathlib.CategoryTheory.Triangulated.Subcategory` and
  `ObjectProperty.ClosedUnderIsomorphisms`: `ObjectProperty.IsTriangulated` and
  `ObjectProperty.IsClosedUnderIsomorphisms`.
- `WeilConjectures.Compactification.Defs`: `Compactification` and
  `HasCompactification`, reexported by the compact-support module. The existence
  theorem recorded in `CompactifiableOverField` is unnecessary here: the choice
  family is indexed precisely by maps admitting compactifications.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`:
  `Scheme.sfIntrinsicDerivedPullback`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport`, whose body is exactly
  `(sfIntrinsicExtensionByZero c.i A).mapDerivedCategory` followed by
  `proEtaleConstantDerivedDirectImage c.g A`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`: the exactness
  and instance declarations used by that termwise extension-by-zero functor;
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` supplies
  `Functor.mapDerivedCategory`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, with independent localization universe.

No source-based stage-2 correction was necessary. The node already records the
stage-1 restriction from the erroneous all-scheme preservation condition to
geometric schemes. Its recorded perfect-complex source tag is stale: Stacks
`more-algebra.tex`, `definition-perfect` (Tag 0657), gives the intended notion,
not the recorded Tag 0A1U. This inherited citation issue does not change the
notion or require a dependency-interface repair.

## Second reading by Q101

Read the entire node, its source `main-20261015/blueprint/sec-trace-formula/
sk-d-setup/_section.md`, every statement-dependency record, and the declarations
listed above. This is a definition node with empty proof and proof-dependency
lists: there is no theorem proof plan to transcribe. The source has no additional
ambient hypotheses beyond its fixed finite-field and coefficient data. Its literal
all-scheme stability clause is the documented source error already corrected by
the reviewed stage-1 node; this reading follows that current node unchanged.

Object/hypothesis/clause checklist, with the final Lean rendering and verdict:

1. Global `q = p^r`, positive exponent, finite base field and fixed algebraic
   closure `k`: `(F : FiniteFieldDatum.{u})`. Opened that structure, not just its
   name; `prime`, `exponent_pos`, `cardinality_eq`, `card_base`, and `isAlgClosure`
   carry precisely the prescribed data. PASS.
2. Prime `l` distinct from `p`: `(l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)`.
   There is no replacement by an arbitrary coefficient ring. PASS.
3. Finite extension `E / Q_l`: `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. Its recorded integers and chosen uniformizer
   define `Padic.coefficientExtensionRing l E n`; no new choice is made. PASS.
4. Positive level and quotient `A`: `(n : ℕ) (hn : 1 ≤ n)` and the very quotient
   above. The body's `letI` installs the existing finiteness theorem, rather than
   adding finiteness as a hypothesis. This let is inside definition data, not
   inside a statement signature. PASS.
5. Base `s = Spec k` and geometric schemes: every stability quantifier uses
   `X : Over (Spec (.of F.k))` with `IsSeparated X.hom`,
   `LocallyOfFiniteType X.hom`, `QuasiCompact X.hom`. Finite type includes
   quasi-compactness; no Noetherian or extra finiteness instance is assumed. PASS.
6. Structure morphism and k-maps: `X.hom` and `(f : X ⟶ Y)` in that over category;
   `f.left` is the underlying scheme map and the commuting equation is part of
   the over-category morphism. The product convention reuses `pullback X.hom
   Y.hom`, documented without a second product definition. PASS.
7. Dimension, reduction, universal homeomorphisms: documented references to
   `topologicalKrullDim X`, `X.nilradical.subscheme`, and
   `(topologically IsHomeomorph).universally f`. Their dependency signatures and
   definitions were opened; they add no extra condition to geometric schemes.
   No duplicate aliases obscure these conventions. PASS.
8. Ordinary unbounded `D(X,A)` on every scheme: all objects `K` use
   `proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E n)`.
   Opened its actual `HasDerivedCategory.standard` localization of intrinsic
   constant-ring `SheafOfModules`; no derived completion or etale-origin filter
   replaces it. The definition remains available for arbitrary schemes. PASS.
9. Bounded constructible finite-Tor objects: every membership test is the existing
   `finiteTorConstructible l E n hn X.left`. Opened its body: intrinsic bounded
   constructibility AND `HasFiniteProEtaleTorAmplitude`. The latter universally
   tests all module sheaves with one interval. `FullSubcategory` supplies all
   ambient morphisms. Its definition has no invertibility restriction, so works
   on arbitrary schemes as requested; on the invertible locus it is exactly the
   intrinsic finite-stage predicate reexported by the recorded dependency. PASS.
10. Full triangulated and isomorphism-closed subcategories only on geometric
    schemes: the first subtype conjunct universally requires
    `(finiteTorConstructible ...).IsTriangulated ∧
    (finiteTorConstructible ...).IsClosedUnderIsomorphisms`. Opened the Mathlib
    classes: zero objects, shifts, distinguished-triangle closure, and repleteness
    have the intended meanings. These are package requirements, not proved
    closure assertions or stability axioms for all schemes. PASS.
11. Pullback preservation for every geometric k-map, without compactifiability
    assumption: the second conjunct quantifies `f` and `K`, requires source
    membership at `Y`, and concludes membership of
    `(sfIntrinsicDerivedPullback A f.left).obj K` at `X`. The dependency is exact
    ordinary identified-constant-coefficient inverse image, not completed pullback.
    Quantifiers and direction agree. PASS.
12. A chosen compactification for each compactifiable geometric k-map: the subtype
    data `cs` return `Compactification f.left` under `[HasCompactification f.left]`.
    Opened the structure: actual `Z`, `g`, `i`, equation `comm`, proper `g`, open
    immersion `i`. Its middle scheme is geometric using structure map
    `c.g ≫ Y.hom`: separatedness, local finite type, and quasi-compactness compose
    with those of `Y.hom`. `c.comm` and `f.w` make `i` a k-map. Therefore the
    ordinary compactification structure already supplies exactly the requested
    geometric compactification, without a missing geometric-middle condition.
    The source map between geometric schemes is quasi-compact, so its open
    immersion is also quasi-compact by the recorded compactification API. PASS.
13. Chosen `Rf_! = Rg_* j_!`, defined on the entire ambient category, preserving
    finite-Tor constructibility: the final conjunct uses
    `(sfIntrinsicCompactSupport (cs X Y f) A).obj K` and the actual chosen `cs`.
    The dependency body uses exact extension by zero termwise and ordinary
    K-injective derived direct image. Nothing is an arbitrary map or a
    Nonempty-selected functor. Compactification independence is not asserted on
    unbounded objects; its separately recorded etale-origin restriction is
    retained. No extra stability for `f^!`, tensor, unit, or proper `f_*` is
    imposed. PASS.
14. `Perf(R)` for every commutative ring: the imported
    `DerivedCategory.IsPerfectRingComplex` is documented as the convention.
    Opened its body: a bounded cochain complex, finite and projective in every
    degree, isomorphic to the object in `D(R)`. It does not restrict `R` to
    coefficient rings or fields. No second perfect-complex predicate is written.
    PASS.

Edge cases checked by reading the definitions and binders: the empty scheme is
included (no `Nonempty X` assumption); zero derived objects are admitted and the
triangulated requirement includes zero; no nonempty indexing set or cover is
added. The minimum coefficient level is `n=1`, with no stronger inequality;
`n=0` is excluded exactly as in the node. Every prime distinct from `F.p` and
every finite-dimensional extension is accepted, without an added characteristic
instance or chosen embedding into a fixed closure. Universes are parametric in
`u`, using the dependency convention: schemes and coefficient ring in `u`, small
site objects in `u+1`, morphisms in `u`, lifted module values in `u+1`, and the
standard derived localization in its inferred larger universe. No equality of
site-object and morphism universes, or extra smallness requirement, is imposed.
Perfect complexes retain their dependency's independent localization universe.

Independent searches (2026-10-17):

- LeanFinder via `msearch.py`: "A coefficient package of bounded constructible
  finite Tor complexes on geometric schemes stable under pullback and chosen
  compact support". Eight hits: chiefly `DerivedCategory.IsGE`, t-structure
  facts and an affine-transition-limit lemma, no package match.
- LeanSearch via `msearch.py`: "Finite coefficient datum with constructible
  derived categories preserved by pullback and chosen compactification
  pushforward". Eight hits: sheaf-pullback finite-limit preservation, finite-map
  base-change facts, finite pretopology, finite simplicial-set pullback, and a
  quasi-coherent module construction. No combined package match.
- Loogle via `msearch.py`: `CategoryTheory.ObjectProperty.IsTriangulated`.
  Twelve hits; opened the class in `Triangulated/Subcategory.lean` and reuse it
  directly for the generic constituent.
- `rg` in Mathlib, the upstream `WeilConjectures` tree, and project `lean/Sheaf`,
  using `GeometricCoefficients`, `constructibleFiniteTor`, `ctf_lowerShriek`,
  `IsGeometricHom`, and `TraceFormulaCoefficientSetup`. Found the upstream
  `SixFunctors/ProEtale/TraceFormula/Defs.lean`; opened its `IsGeometric`,
  `IsGeometricHom`, `Ctf`, and entire `GeometricCoefficients` field list.
  The last is NOT the node's package: it requires unit, tensor, exceptional
  inverse-image, and proper direct-image stability, in addition to pullback
  and exceptional direct image, for an abstract coefficient category. It also
  uses a different published constructibility predicate and an intrinsic
  lower-shriek functor instead of chosen compactification data. Recording it
  as an exact existing match would strengthen this node. Its elementary
  geometric notion is rendered directly using the dependency morphism-property
  classes, not redefined. Existing finite-Tor, constructibility, derived, and
  perfect notions were found and reused as listed above. No exact package
  declaration or existing DAG node carrying this exact package was found.

Mismatches and repairs: the initial delivery files and report were entirely
missing, so this continuation reconstructed them instead of claiming to validate
nonexistent work. The upstream similarly named package was rejected as an
inexact, stronger match. A documentation reference to `c.fac` was corrected to
the actual compactification field `c.comm`. The node's Lean signature is taken
verbatim from the declaration keyword `def` up to `:=`. The mathematical node,
its statement dependencies, and all dependency records are unchanged. There are
no new definition nodes or dependency modules to review. No target or unit
statement was changed.

Validation: `scompile.py Q101 sk-d-setup` compiled the delivered module cleanly,
including separate overlay checks of the intrinsic extension-by-zero exactness
and compact-support modules. No errors or warnings; no unbound variables,
file-local notation/instances, private definitions, proof declarations, or
hollow data. All lines are at most 100 characters. The compactification choices
are subtype inputs, never chosen from a postponed mere existence assertion.
