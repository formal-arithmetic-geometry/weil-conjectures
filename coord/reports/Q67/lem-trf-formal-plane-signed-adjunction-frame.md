## Worker report

The module `Sheaf.TraceFormula.FormalPlaneSignedAdjunctionFrame` states
`AlgebraicGeometry.exists_formalPlaneSignedAdjunctionFrame`, with one postponed
proof. It introduces only notation-free data and maps for the formal plane
presentation and signed frame already introduced by this node. All definitions
have real data. The natural-language proof in the theorem docstring follows all
six DAG steps, including the negative orientation and the two signed fractions.

Hypothesis correspondence:

- `k`, `[Field k]`, `[IsAlgClosed k]` are the algebraically closed coefficient field.
- `S`, `[CommRing S]`, `[Algebra k S]`, `[Algebra.FiniteType k S]`, and
  `[_root_.IsReduced S]` give precisely the reduced finite-type algebra. The
  recorded `RingHom.FiniteType (algebraMap k S)` is equivalent to the displayed
  `Algebra.FiniteType k S` (Mathlib's `RingHom.finiteType_algebraMap`).
- `hpure : (Spec (CommRingCat.of S)).IsPureDimension 1` uses the dependency's pure
  dimension definition. `hlci : Algebra.IsLocalCompleteIntersection k S` uses
  its actual localized-global-complete-intersection definition.
- `p : Ideal S`, `[p.IsMaximal]`, and `hresidue` give the rational maximal ideal;
  `Localization.AtPrime p` is A. `Algebra.LocalCompletion A` unfolds to the
  maximal-ideal `AdicCompletion`; it is R, not a separately chosen complete ring.
- The reduced-completion instance expresses that the fixed formal quotient is
  reduced. Surjectivity and the kernel identity identify that quotient with R,
  so this is equivalent to the node's reduced `T/(f)` assumption.
- `J`, `hJ : J.IsNormalized` fix the adjunction line and its canonical transitions
  from the recorded adjunction construction. Its affine sections localized at p
  are the stalk K_A; `completedConormalSource` is R tensor over S with those
  sections, canonically R tensor over A with K_A. The derived-category instances
  are the same implementation choices used by the recorded comparison interface;
  they impose no geometric hypothesis or extra equality of universes.
- Every `FormalPlaneEquation` contains exactly the specified nonzero f in the
  variable ideal, quotient map T to R, its surjectivity and kernel (f), and its
  continuous local k-algebra structure. This packages the fixed complete local
  quotient isomorphism. It does not assume regularity or a conormal basis.
- Each field L has the R-algebra map theta, its restrictions to A and S, and the
  scalar tower identities. A separate k-algebra structure is unnecessary: the
  composite k to R to L supplies it. `IsCompletedConormalGeneric` means exactly
  that the A-kernel is a minimal prime and its point lies in a smooth open. Pure
  dimension one fixes the smooth dimension. All scalar structures are the same
  restrictions of theta; the tower binders do not add mathematical hypotheses.

Conclusion correspondence:

- `C` is the existing normalized completed comparison system. The theorem asserts
  its existence, rather than assuming the desired isomorphism or choosing an
  arbitrary map. `C.extension` asserts that its derivation is the continuous
  extension in the recorded predicate; the first conjunct asserts uniqueness
  among all such derivations.
- For every raw plane equation the theorem supplies `h`, regularity of its single
  equation. `P.presentation h` inserts this conclusion into the existing general
  formal presentation without changing the equation, map, or kernel.
- `C.formal (P.presentation h)` supplies a basis indexed by Fin 1 of the actual
  `Algebra.Extension.Cotangent = J/J^2`. The explicit existential `q` identifies
  its zeroth element with the class of f. Thus the basis is the asserted f-bar,
  not an unnamed isomorphic copy of R.
- `formalPlaneComparison C P h` is Phi: it is obtained from `C.comparison` by the
  affine equivalence. Its target `formalPlaneDeterminantModule` is the global
  sections of `(exterior^1 conormal)^dual tensor exterior^2 R^2` after associated
  sheafification. On the affine spectrum this is exactly
  `Hom_R(J/J^2,R) tensor_R exterior^2_R(R dx + R dy)`. In particular neither term
  has been replaced by a coordinate-free copy of R. The first exterior power is
  canonically the conormal module itself.
- `alpha` is a section of the actual dual of that first exterior power.
  `IsFormalPlaneDualGenerator` says it evaluates to 1 on the class of f.
  `formalPlaneOrientation` tensors it with the wedge of the two standard
  coordinate sections, in the order dx,dy. It is the node's positive w.
- `B : Module.Basis (Fin 1) R (completedConormalSource J)` gives the basis element
  eta as `B 0`. Its image is explicitly `-formalPlaneOrientation`. The next
  conjunct states uniqueness even among all elements with this image.
- `formalPlaneCoordinate C.derivation P 0` and index 1 are precisely e_x,e_y:
  apply the completed derivation to the quotient coordinate and extend its
  coefficients along theta. `formalPlanePartial P 0` and index 1 are a,b, using
  the recorded `MvPowerSeries.pderiv`, followed by the quotient and theta.
- The disjunction a nonzero or b nonzero is exactly `(a,b) != (0,0)`. It guards
  the exact-sequence, determinant, and signed-fraction conclusions. It does not
  guard or replace the preceding algebraic smooth-comparison assertion.
- `genericJacobian` is the map from Fin 1 to Fin 2 given by the column (a,b);
  identify Fin 1 to L with L by evaluation at 0. `genericAugmentation` sends the
  two standard vectors to e_x,e_y, by `augmentation_eq`. Its linearity gives
  `(u,v) -> u e_x + v e_y`. Injectivity, `Function.Exact`, and surjectivity are
  the two-zero-ended short exact sequence, without any flatness assumption on
  theta.
- `gamma` has target M_L itself. `IsCompletedConormalSmoothComparison`, using
  the explicit inverse of `exteriorPower.oneEquiv`, identifies it with the
  actual algebraic smooth-locus map. `delta` also has source M_L, and
  `IsCompletedConormalGenericDeterminant` composed with `oneEquiv` gives the
  complete relation-first lift-independent wedge convention, not only its
  values on a pair of vectors.
- The identity for every completed source element t says delta composed with
  gamma equals Phi extended to L. `formalPlaneGenericSource` performs the tensor
  associativity/extension to L, including on eta; the right-hand tensor is the
  extension of Phi(t). Thus the map is gamma_L = delta inverse composed with Phi_L.
- The next two conjuncts are exactly delta(e_x)=b Phi_L(eta_L) and
  delta(e_y)=-a Phi_L(eta_L). The final two implications are the two displayed
  inverse fractions and their nonvanishing. All inverse scalars lie in L.
- Algebraic and continuous formal presentation compatibility are retained in
  `C.algebraic_changes`, `C.lift_maps`, and `C.formal_changes`, using the actual
  conormal change maps and the normalized determinant predicate. Its
  `formalComparison T U = (C.comparison T).symm` followed by `C.comparison U`
  composes through the common algebraic source for any three presentations.
  Each `gamma` is normalized by the same algebraic smooth comparison; its
  normalization on all source sections fixes that map. The simultaneous system
  C and these conditions express independence of the formal presentation.
  There is no assertion that the coordinate-dependent basis elements agree.

Dependency declarations used (signatures and docstrings read in their sources):

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`; the existing
  `Algebra.LocalCompletion` from the completed-local-presentation interface.
- `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`:
  `FlatLCIAdjunctionSystem`, `.IsNormalized`, `flatLCITwoTermLine`, and
  `exists_flatLCICanonicalAdjunction` (the latter remains a proof input).
  The supplied system and `.IsNormalized` are cited through their live definition
  owner `def-sfb-flat-lci-adjunction-system`, rather than relying on the existence
  theorem node to own these notions.
- `Mathlib.RingTheory.MvPowerSeries.Basic` and `.Derivative`: `MvPowerSeries`,
  `MvPowerSeries.X`, `MvPowerSeries.pderiv`.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` and `.ExteriorPower.Basic`:
  `exteriorPower`, `exteriorPower.oneEquiv` and the existing sheaf exterior
  construction `Scheme.Modules.exteriorSheaf` and `.exteriorSheafSection`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct.map`,
  `LinearMap.baseChange` (inside the comparison interface), scalar towers.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, its universal derivation interface.
- `Sheaf.RingTheory.CompletionKaehlerDifferentialComparison`:
  `Algebra.IsCompletedDifferentialExtension`,
  `Algebra.completion_kahler_differential_comparison`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Sheaf.TraceFormula.CompletedConormalDeterminantComparison`: the existing
  `CompletedConormalFormalPresentation`, `CompletedConormalFormalData`, their
  actual conormal and generic maps, `completedConormalSource`,
  `CompletedConormalDeterminantComparison`,
  `IsCompletedConormalGeneric`, `IsCompletedConormalSmoothComparison`,
  `IsCompletedConormalGenericDeterminant`,
  `CompletedConormalDeterminantComparison.formalComparison`. These definitions
  are now cited through `def-trf-completed-conormal-comparison-data`, the new
  definition-only owner of the existing module. The inhabitation theorem
  `exists_completedConormalDeterminantComparison` is a proof dependency only;
  its `Nonempty` conclusion is not used to state this theorem.

Searches performed before writing:

- `msearch.py ... leanfinder` queried "Signed completed adjunction frame for a
  formal plane hypersurface with generic inverse dx divided by f_y or minus dy
  divided by f_x". Eight irrelevant manifold/derivation results, no exact match.
- `msearch.py ... loogle` queried `"KaehlerDifferential", "determinant"`.
  Zero results.
- `msearch.py ... grep` queried
  `adjunction.*frame|conormal.*determinant|poincare.*residue`. One irrelevant
  `Mathlib/Topology/Order/Category/FrameAdjunction.lean` documentation hit.
- `msearch.py ... leansearch` queried "A generator of the canonical module of a
  plane hypersurface maps to dx divided by partial f partial y". Results were
  ordinary polynomial differentials, the ideal cotangent quotient, and
  polynomial generator maps; none states the completed signed frame.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `signedAdjunction|signed_adjunction|formalPlane|formal_plane|Signed.*Frame`
  found only `FormalPlaneAdjunctionLattice`, a branch/lattice comparison with
  a different statement. Read its input and conclusion to exclude reuse.
  The prescribed upstream grep for the item id had no results.
- DAG searches for the plane/signed notion found this node, its parent lattice
  theorem, and its general completed comparison prerequisite. The latter is
  reused; no duplicate general determinant, differential extension, or
  polynomial derivative is defined.

Edge cases checked before and during the second reading:

- f=x has a=1,b=0: only the -dy/a fraction is required; f=y has a=0,b=1:
  only dx/b is required. Neither missing denominator excludes a presentation.
- f=xy on the two generic branches gives dx/x and -dy/y, respectively.
- When both coefficients are nonzero the relation makes the fractions equal;
  when both are zero, the conditional fraction/exactness clauses assert nothing.
  The canonical comparison, frame and derivation remain asserted.
- Characteristic two is allowed: exterior alternatingness gives the determinant
  calculation, and the displayed negative signs specialize without division by 2.
- In characteristic p, f=x^p-y^(p+1) has one zero formal partial. The nonzero
  partial branch remains covered; no inverse is required in R itself.
- f=0 and a unit f are expressly excluded, as in the node; f=x^2 with a
  nonreduced quotient is excluded by reducedness. No generic-smooth point is
  invented if the generic predicate has no instance.
- Empty/zero S cannot supply the rational maximal ideal. The definition of pure
  dimension itself keeps its empty-scheme convention. All variables and universes
  are explicitly bound; fields use the same universe convention as the recorded
  comparison, and no site universe equality is added.

No mathematical statement correction or dependency interface repair is needed.
The repair introduces the definition-only node described below. The auxiliary
Lean declarations in the delivered module still belong to the plane presentation
and maps specified by the item itself.

## Second reading by Q67

A separate pass by this worker reread the node, source wedge formula, the full
comparison-system signature, and every delivered declaration. No other agent
was started, as the dispatcher expressly forbids delegation; the maintainer's
independent review remains the independent review.

The reading found an implication-precedence issue in the initial skeleton:
`SmoothComparison and nonzero-column -> ...` would have made smooth normalization
only an antecedent. It was changed to `SmoothComparison and forall nonzero-column,
...`, so smooth normalization is actually asserted. The conormal basis condition
was also made explicit by naming a representative q equal to f and identifying
its class with the basis element. Its Fin 1 index is explicitly typed to avoid
an instance-search failure on the presentation's reducible rank projection.

The final reading checks that regularity is concluded, the negative frame is
unique, the generic determinant retains the complete wedge formula, both
conditional nonvanishing assertions are present, and compatibility is supplied
by the single existing comparison system. The clause correspondence above
records the affine/sheaf and first-exterior-power identifications explicitly.
Compilation uses only scompile.py; the final clean result and preflight are
recorded by the delivery wrapper.


## Returned delivery repair: H2

Returned immutable head: `2b32bdcd9e04`. The reviewer accepted the mathematical
statement and returned its definition ownership. The repaired item removes the
previously added theorem node `lem-trf-completed-conormal-determinant-comparison`
from statement dependencies and adds `def-trf-completed-conormal-comparison-data`.
The original theorem remains in proof_deps, since the six-step proof uses its
existence assertion. The item also directly cites the already-landed
`def-sfb-flat-lci-adjunction-system`, the definition owner of the supplied `J`
and `J.IsNormalized`. The original adjunction theorem reference remains as on
the live base; no original source text or mathematical statement was changed.

The new definition node attaches `existing: true` to the existing module
`Sheaf.TraceFormula.CompletedConormalDeterminantComparison` and its definitions.
This is the same attachment pattern used by the live adjunction-system owner:
there is no duplicate module, no extracted private copy, and no definition
chosen from the theorem's `Nonempty` conclusion. The theorem declaration is
excluded from the new node's `lean.declarations`. This attachment is the
module ownership requested by H2 and is permitted explicitly by brief-stage2
section 1(A) for notions already implemented but lacking a definition node.

The retained sandbox was compared with current main's node: only the old added
statement dependency and the delivered lean record differed. The repaired node
was rebuilt from the current base, retaining its source, statement, proof,
proof dependencies, and all other metadata verbatim. The new lean note documents
H2 instead of repeating the erroneous claim that importing a theorem's module
makes that theorem a statement dependency. The delivered theorem's signature,
its helpers, and its single sorry are byte-for-byte unchanged from the returned
version. Every repair is in the sandbox; the wrappers perform the rebase.

## New nodes

`def-trf-completed-conormal-comparison-data` records the actual existing type of
supplied completed-conormal comparison systems and its presentation, map,
augmentation, source-line, and normalization definitions. Its source is the
agent-formulated interface around Stacks 08SL, 0C52, 0E9Y, 0E9Z, 0FJX and 0FJY;
the sources do not assert existence of this complete record verbatim. Its
statement introduces the field, algebra and completion, polynomial-local and
continuous formal regular presentations, two-term modules and associated sheaf
complexes, actual ideal-class/differential maps, the adjunction source and
smooth generic predicate, ordered-wedge determinant normalization, and every
field of `CompletedConormalDeterminantComparison`. It ends by distinguishing
the supplied-system type from its inhabitation theorem. It has no proof and
introduces no new Lean data. Its `lean` record points to the exact existing
structure signature and lists the existing definitions in that module, omitting
`exists_completedConormalDeterminantComparison`.

The recorded searches preserve the raw outputs of the three new msearch calls:
LeanSearch for "Data for normalized determinant comparison of algebraic and
continuous formal conormal presentations after completion" gave eight scalar
or Jacobian determinant results; Loogle for `"KaehlerDifferential", "determinant"`
gave zero hits; Mathlib grep for
`CompletedConormal|conormal.*determinant|determinant.*conormal` gave zero hits.
DAG grep found only the theorem node carrying the existing declarations;
blueprint_refs search for "completed conormal" gave zero blueprint nodes and
its ancestor command returned `lem-trf-local-term-locality`. Project grep found
the exact existing declarations in Sheaf and no upstream match. Thus a new
implementation would duplicate the library, whereas a definition-only DAG
attachment is missing and required. The new node's mathlib_searches includes
these raw tool results plus the project/DAG and blueprint searches.

The new node's field correspondence was reread against the full existing source:
`CompletedConormalAlgebraicPresentation` retains its rational centre, regular
kernel generators and surjection; `CompletedConormalFormalPresentation` retains
continuity, locality and the rank equality; `CompletedConormalModel` and
`CompletedConormalMap` retain actual modules and chain maps. The source, affine
section, generic-smooth and smooth-comparison predicates retain the exact
coefficient structures and differential-section values. `CompletedConormalFormalData`
retains the entire relation formula, augmentation, exactness and conormal basis;
its generic augmentation and Jacobian are the existing finite linear combinations.
The determinant predicate retains the quantified dual orientation and every
choice of quotient lifts. Finally, every comparison-record field is included:
derivation/extension, formal data, algebraic and formal comparisons, algebraic
exactness and bases, lifts, lift maps, lift independence, algebraic and formal
changes, and the simultaneous generic smooth/determinant normalization.
`formalComparison` is the already-defined composition through the common source.
No existence assertion has been turned into a definition.

Repair rereading: H2 is resolved at both ownership sites. The new node's
statement-dependency list equals exactly its bracketed definition citations;
its branch record is `existing: true`, with no `file` and with its real module.
The live adjunction definition record was read in full and is reused without
editing it. All mathematical edge cases checked in the accepted first review
remain unchanged; the general data attachment also permits zero ranks, empty
relation lists and empty wedges. Compilation, dry-run preflight and redelivery
are repeated with the prescribed wrappers.
