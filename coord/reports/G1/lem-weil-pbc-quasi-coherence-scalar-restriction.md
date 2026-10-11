## Worker report

The module states `quasiCoherent_iff_restrictScalars`, expressing equivalence of `SheafOfModules.IsQuasicoherent` before and after `SheafOfModules.restrictScalars`. It imports Mathlib change-of-rings and quasi-coherent sheaf modules. The variables explicitly bind a site `C`, category structure, Grothendieck topology `J`, sheaves of rings `R,A`, ring morphism `α`, and the weak-sheafification/local-bijectivity instances required by Mathlib's local quasi-coherence predicate. The theorem proof is `sorry` as required.

Dependency declarations used: `AlgebraicGeometry.Scheme` for the scheme notion (not used directly in the categorical rendering); `SheafOfModules.IsQuasicoherent` and `SheafOfModules.restrictScalars` from Mathlib. The source statement's quasi-coherent-algebra condition has no direct Mathlib predicate for a sheaf-of-rings algebra, so this categorical rendering leaves that condition implicit in the ambient sheaf morphism.

Edge cases checked: empty indexing families are allowed by Mathlib's coproduct presentation; restriction of scalars is defined for arbitrary sheaf-ring morphisms. Searches with msearch/rg found no existing theorem relating quasi-coherence to scalar restriction.

STATEMENT-DISPUTED: the source's explicit hypothesis that the algebra sheaf is quasi-coherent as an O-module cannot be represented with the available Mathlib sheaf-of-rings API; the written theorem therefore abstracts over a general ring-sheaf morphism.

## Earlier second reading (a previous round; superseded)

The declaration compiles and its hypotheses and biconditional conclusion match the categorical restriction-of-scalars formulation. The source algebra quasi-coherence hypothesis remains unrepresented, as noted above.

## Second reading by G1

The worker's disputed rendering and the earlier reading above are superseded by this
reading. The node itself agrees with Stacks 0H88 and has not been corrected or changed.
I read the source in `/home/ubuntu/c1-stacks-review/morphisms.tex`, lines 1844–1901,
including the whole lemma and both directions of its proof. Its standing assumptions
are precisely a scheme and a quasi-coherent commutative structure-sheaf algebra; it
requires no Noetherian, finiteness, separation, base-field, or characteristic condition.

Clause-by-clause list of the node and its Lean rendering:

- Scheme S: `(S : AlgebraicGeometry.Scheme.{u})`. PASS after repair. The worker had
  an arbitrary site instead, which does not supply the affine-local scheme argument.
  I opened `def-pc-scheme` and Mathlib's `Scheme` declaration: the local-affine locally
  ringed space is exactly the dependency's scheme notion.
- The open-set site of S: `Opens.grothendieckTopology S`, rather than arbitrary J.
  PASS after repair; all sheafification/local-bijectivity instances are inferred on
  this site, so there are no extra instance hypotheses in the statement.
- A sheaf of commutative O_S-algebras: the binders
  `A : Sheaf (Opens.grothendieckTopology S) CommRingCat.{u}` and `α : S.sheaf ⟶ A`.
  PASS after repair. The worker used an arbitrary RingCat sheaf and an arbitrary R.
  Composing with `forget₂ CommRingCat RingCat` only exposes the same rings to the
  module API; it neither changes the algebra nor drops commutativity. These are the
  unpacked data of the already landed `Scheme.CommAlgebraSheaf = Under S.sheaf`;
  I opened its module and node and introduce no new definition or private copy.
- A is quasi-coherent as an O_S-module: `hA` states `IsQuasicoherent` of
  `restrictScalars` applied to `SheafOfModules.unit` of the RingCat image of A.
  PASS after repair. This hypothesis was missing, despite being explicitly required
  by both node and source. I opened the definitions of `unit` (A over itself),
  `restrictScalars` and `restrictScalarsObj` (the action via α), and the landed
  `CommAlgebraSheaf.toModule`, which uses exactly this expression.
- An A-module G: `G : SheafOfModules.{u} ((sheafCompose ...).obj A)`. PASS. I opened
  `def-weil-sheaf-of-modules-category`, its Mathlib match, and `SheafOfModules`: its
  sectionwise action, semilinear restrictions, and linear morphisms match the node.
- G quasi-coherent over A means a local presentation by arbitrary direct sums of
  copies of A: `G.IsQuasicoherent`. PASS. I read `QuasicoherentData`, `Presentation`,
  and `free`: a covering by opens with generating sections and relations gives the
  displayed cokernel presentation, and `free I` is the coproduct of `unit A` over I.
  This is equivalent to a neighbourhood for every point, without any finite-index
  requirement. The reverse passage from cokernel presentations is already Mathlib's
  `presentationOfIsCokernelFree`; no replacement predicate is needed.
- Underlying O_S-module: `(SheafOfModules.restrictScalars ((sheafCompose ...).map α)).obj G`.
  PASS after repair; its scalars are now the actual structure sheaf, not arbitrary R.
- Conclusion in both directions: `G.IsQuasicoherent ↔ (...obj G).IsQuasicoherent`.
  PASS, in the node's order. I opened `pqf-def-coherent` and its recorded module
  `Sheaf.AlgebraicGeometry.Coherent`: quasi-coherence deliberately reuses Mathlib's
  local-presentation predicate; the affine-local tilde form is the equivalent scheme
  characterization (Stacks 01IA), not another predicate or the coherent predicate.
  The quantifiers are S, A, α, hA, G, then the biconditional, as required.

Edge cases: no nonempty-space or nonzero-ring hypothesis; the empty scheme is included
and local presentations are vacuous there. The zero algebra and zero module are
included. Generators/relations are arbitrary types, including empty types, and no
finite, positive-n, characteristic, field, or Noetherian assumption is made. All
universes and variables are explicitly bound (`universe u`); S, ring sections and
module sections can be placed in any common universe u, so larger modules/algebras
are covered after enlarging the universe of the scheme. The presentation index types
may be taken in u because each section module lives in u; there is no extra bound on
cardinality or finite-presentation condition. No definition contains sorry; the only
sorry is the named theorem, whose docstring now gives every one of the node's six
proof steps with the dependencies they use.

Independent searches, using different wording from the worker:

- LeanFinder via msearch: `quasicoherent module over algebra sheaf underlying structure
  sheaf`. Eight hits, including ModuleCat.tilde, Scheme.Modules, QuasicoherentData,
  section-module instances; none states this equivalence.
- LeanSearch via msearch: `local free presentations scalar restriction quasicoherent
  algebra on scheme`. Service unavailable (Internal Server Error); no mathematical
  verdict inferred from its failure.
- Loogle via msearch: `SheafOfModules.restrictScalars, SheafOfModules.IsQuasicoherent`.
  Zero hits.
- rg of scalarRestriction/scalar_restriction/restrictScalars in Mathlib's
  Sheaf/Quasicoherent.lean, the project's lean/Sheaf and slopmaster2 WeilConjectures.
  Found the known change-of-rings API, the landed CommAlgebraSheaf.toModule, and
  constant-coefficient sheaf scalar-restriction declarations; none is the desired
  quasi-coherence equivalence. Opened the upstream ModuleCat/Sheaf/RestrictScalars
  module to distinguish its constant-coefficient sheaves from this ring-sheaf API.
  Also checked the full new declaration name against dag/lean_names_upstream.json,
  upstream Lean, and lean/Sheaf: no collision.

Repairs: replaced the arbitrary site/RingCat formulation by the precise scheme,
commutative algebra, structure map and explicit quasi-coherence hypothesis. Removed
unnecessary instance binders, moved the file from the nonconforming Weil directory
to AlgebraicGeometry, put the theorem in Scheme.Modules, and added the copyright,
module source docstring, and complete six-step proof docstring. Updated lean.statement
verbatim from the signature. No new nodes or dependency modules are needed: all
notions are already supplied by the dependency records and Mathlib. The node's
statement, stmt_deps, proof and proof_deps are unchanged.

Validation: scompile.py compiled the repaired module on the server in 3.4 seconds,
exit code 0, with no errors or warnings. Checked all binders and universes by eye.

## Reviewer fix (R-qsr1450)

The second reading kept the algebra unpacked as `A : Sheaf _ CommRingCat` with a separate
`α : S.sheaf ⟶ A` and an inlined copy of `CommAlgebraSheaf.toModule` in `hA`. Per the
QUASI-COHERENT O_X-ALGEBRAS line the statement now uses the shared form
`A : S.CommAlgebraSheaf` with `hA : A.toModule.IsQuasicoherent`, `G` over
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj A.right` and scalar restriction along
`A.hom`, word for word as K1 c42e1122f. Content unchanged (definitionally the same data).
Not a restatement of K1 162f49708 clause (1): that is the special case `A = u_* O_U` for an
affine `u`, and its proof cites this node.
