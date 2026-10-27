## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleClosureFibreAvoidance` states
`AlgebraicGeometry.AlgebraicSpace.constructible_closure_geometric_fibre_avoidance`.
Its only proof is `sorry`; no definitions or proofs are added. The declaration docstring
includes all twelve proof steps and their named inputs from the unchanged DAG proof.

Clause-by-clause correspondence:

- The arithmetic base is `T : Over (Spec (.of (ULift.{u} ℤ)))`. Its underlying scheme is
  `T.left` and its structure morphism is `T.hom`. The universe lift is the usual spectrum
  of the integers in the test schemes' universe, not a restriction to characteristic zero.
- Nonemptiness is `[Nonempty T.left]`. Finite type is `[LocallyOfFiniteType T.hom]` and
  `[QuasiCompact T.hom]`, the recorded Mathlib conjunction. The name `D = dim T` is
  `(D : ℕ) (hD : topologicalKrullDim T.left = (D : WithBot ℕ∞))`. Finite-type arithmetic
  schemes have finite dimension; this binder only names that dimension.
- `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))` retains general algebraic spaces.
  `q : X.obj.obj ⟶ yoneda.obj T` is their morphism to the represented scheme T.
  Viewing X over the integers via q is the same original datum, with no schematicness
  condition on X and no extra structure on the morphism.
- Smoothness is `hq : MapToSchemeIsLocally (@Smooth) X T q`, tested on all representable
  etale scheme charts. Surjectivity is `hsurj : Function.Surjective (mapPoint q)` on the
  usual point classes. This is surjectivity of algebraic spaces, allowing all scheme
  base changes, and does not require representability by schemes. In particular the
  existing `IsSurjective` predicate, which additionally demands scheme representability,
  is deliberately not imposed on q.
- Separatedness is `hsep : MapToSchemeIsSeparated X T q`, namely a relative diagonal
  representable by closed immersions. Finite presentation is exactly `hlfp`, the local
  finite-presentation chart test, `hqc : MapIsQuasiCompact q`, and `hqs`, quasi-compactness
  of `pullback.diagonal q`, i.e. quasi-separatedness. No properness hypothesis occurs.
- The common nonnegative fibre dimension is `r : ℕ`. For EVERY `Ω : Type u` with
  `[Field Ω] [IsAlgClosed Ω]` and EVERY `t : Spec (.of Ω) ⟶ T.left`, `hpure` says that
  every irreducible component C of the point space of the actual presheaf pullback
  has `topologicalKrullDim C = r`. Thus purity is on the original geometric fibre,
  not merely on an atlas, the ordinary fibre, or its total dimension. This is the
  explicit component condition, using Mathlib's existing irreducible components and
  dimension rather than creating a second definition of pure dimension.
- The base-change arrow is `yoneda.map (Over.homMk
  (U := Over.mk (t ≫ T.hom)) t rfl)`. The pullback of q along it is X_t. Its first
  projection gives the canonical `mapPoint` into X; no arbitrary map is chosen.
- `Z : Set (Point X.obj.obj)` and `hZ : Topology.IsConstructible Z` give precisely
  the constructible subset of the existing atlas topological space. Z is not assumed closed.
- `c : ℤ` and `hc : (D : ℤ) < c` express the original integer bound c > D.
- `hfibre` bounds the dimension of the CLOSURE, inside the geometric-fibre point
  space, of the INVERSE IMAGE of Z under that first projection. Its bound is
  `if c ≤ (r : ℤ) then (((r : ℤ) - c).toNat : WithBot ℕ∞) else ⊥`.
  Mathlib dimension has values `WithBot ℕ∞`, so an integral upper bound below zero
  means the empty space, encoded exactly by ⊥. The conditional prevents natural
  subtraction from silently replacing a negative upper bound by zero.
- The first conclusion says that for every such geometric point, the range of the
  geometric-fibre projection is NOT contained in `closure Z`. This is exactly the
  assertion that no entire geometric fibre lies in the global closure.
- The second conclusion gives `W : OpenSubspace X` with `pointImage W.val.ι =
  (closure Z)ᶜ`; this identifies the actual open subfunctor with the specified open
  complement, not an unspecified smaller smooth open. The open-subspace definition
  already means it is an algebraic space. Smoothness is the chartwise condition
  `∀ U a, IsEtale a → Smooth (yoneda.preimage (a ≫ W.val.ι ≫ q)).left`.
  Surjectivity is `Function.Surjective (mapPoint (W.val.ι ≫ q))`.
- The explanatory group-space and integral terminology in the node introduces no
  group action or integrality hypothesis into this independent dimension lemma.
  There is no group object in the Lean statement. There is no assertion that the
  global closure commutes with base change.

Dependency declarations used (modules read, including signatures and docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms, `Spec`,
  and `Spec.map` (def-pc-scheme, def-weil-affine-spectrum).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` (def-trf-algebraic-space).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (def-sbc-locally-finite-presentation).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its QuasiCompact import:
  `LocallyOfFiniteType`, `QuasiCompact` (def-weil-finite-type-morphism).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `AlgebraicSpace.OpenSubspace`
  (def-a1-space-open-subspace).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `pointImage`, and its imported `Point` (def-a1-space-point-topology).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`
  (def-kun-topological-krull-dimension).
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`
  (def-weil-constructible-subset, whose mathlib_match is its binding).
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`,
  `MapIsQuasiCompact`, `MapToSchemeIsLocally`, `MapToSchemeIsSeparated`.
  Its already landed owning node `def-sfb-proper-curve-moduli` is added to stmt_deps
  as authorized by the standing brief, to reuse those canonical point-map and chart
  interfaces. No declaration or definition is copied or repaired.

The module imports all recorded proof-dependency modules that are currently stated,
with plain imports where they are not statement imports. Unstated proof prerequisites
have no imports: lem-sfb-qc-space-affine-etale-atlas, lem-sfb-noetherian-space-topology,
lem-sfb-space-quasifinite-source-dimension-bound, lem-sfb-space-field-extension-dimension,
lem-sfb-generic-residue-transcendence-dimension-bound,
lem-sfb-space-etale-atlas-topological-dimension. These do not prevent stating the lemma.

Edge cases checked before writing: the base cannot be empty, as required. An empty Z
satisfies the fibre bound even when r-c < 0 and has complement X. When r=0, c>D≥0
makes the bound negative, forcing Z empty rather than allowing a zero-dimensional bad
locus. For r-c=0 the bound allows finite zero-dimensional fibre loci. For c>r it
forces empty geometric inverse images; there is no natural-subtraction truncation.
Disconnected and reducible bases and fibres are allowed; purity is checked component
by component. Geometric fields range over arbitrary algebraically closed fields in
Type u, not just a preselected algebraic closure. No commutativity, irreducibility,
properness, or separatedness of an atlas was silently required.

Sources read: the complete node statement and twelve-step proof; all statement-dependency
records and source declarations; Stacks morphisms.tex lemma-dimension-formula (02JU),
lemma-dimension-formula-general and lemma-alteration-dimension-general (0BAG);
spaces-morphisms.tex lemma-dimension-formula-general (0BAX). Deligne's PDF is marked
locally WANTED in the node; the existing fully written source-based argument is retained.

Searches for an existing full statement:

- `msearch.py ... leanfinder "constructible locus fibre codimension closure dimension
  smooth arithmetic base"`: eight hits on smooth loci, standard-smooth relative
  dimension and constructible-set data, none the avoidance statement.
- `msearch.py ... loogle "topologicalKrullDim, Topology.IsConstructible"`: zero hits.
- `msearch.py ... grep "closure.*[fF]ib[er]|[fF]ib[er].*closure" AlgebraicGeometry`:
  zero hits.
- `rg` of WeilConjectures and Sheaf for the item id and proposed declaration name:
  no existing declaration. Broader searches for algebraic-space morphism predicates,
  point maps, open subspaces, fibre purity and dimension found the reused interfaces
  listed above, but no statement of this lemma.
- `rg` of Mathlib topology for PureDim/Equidimensional and of the project for
  pure dimension: only the scheme-specific `Scheme.IsPureDimension` predicate was
  found, so the fibre point-space component condition is written explicitly.

No statement correction, no new nodes, no dependency repairs, no disputed statement.
Initial scompile succeeded except a docstring-spacing linter warning; the extra blank
line at the end of the proof docstring was removed for the final compile.

## Second reading by Q22

The dispatcher explicitly prohibits starting other agents; this is a second pass by
this worker, not a claim of independent review. The maintainer supplies the independent
review. Reopened the node and Lean module and compared every clause as above. In
particular checked: T.hom is the arithmetic finite-type map; q has a general algebraic
space source; mapPoint surjectivity avoids inadvertently requiring a schematic source;
finite presentation includes the diagonal's quasi-compactness; the geometric pullback
is along t with its original map to the integer base; every component has dimension r;
negative r-c uses bottom; the fibre closure and global closure occur in distinct
spaces; both the fibre-avoidance conclusion and the specified open complement's two
properties are present. All binders and the universe u are explicit, autoImplicit is
false, no file-local notation/instance/definition occurs, and every line is at most
100 characters. The group/integral explanatory text does not introduce a hypothesis.
The sole change on this pass was the docstring-spacing repair. No mathematical mismatch
was found and no statement/proof correction was needed.
