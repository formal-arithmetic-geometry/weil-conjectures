## Worker report

The module states lemma 1266, finite-projective summand inverse equations and
presentation independence. It introduces one specialization helper, not a second
projection-map construction: `ringedProjectionFormulaSummandArrows` applies the
published `ringedProjectionFormulaArrows` to a coefficient sheaf in degree zero.
The only postponed proof is `SheafOfModules.ringedProjectionFormula_projective_summand`.
Its docstring gives the node's three-step naturality, retract, and uniqueness proof.

Hypotheses and clauses:

- The ringed-topos morphism and canonical derived operations are exactly the
  parameters of the published arrow definition: `uInv`, `uPush`, `adj`, finite-limit
  preservation, `I`, `c`, `uStar`, `hobj`, `hmap`, `LF`, `epsilon`, `hLF`,
  `PR`, `PS`, `hPR`, `hPS`, `TR`, `TS`, `rR`, `rS`, `k`, `V`, `am`, `RF`,
  `eta`, `hRF`, `computeR`, `computeL`, `adjD`, and `canonicalAdj`.
  These specify the ordinary module pullback, the canonical derived tensor
  comparison on K-flat representatives, and the canonical derived adjunction;
  they are inherited data, not arbitrary replacement maps or extra exactness.
  Site and coefficient universes are `u`, the derived-category universe is `w`,
  matching the dependency's chosen small-site convention.
- `E`, `K`, `hK`, `repE` are the given derived object and its chosen K-injective
  representative, exactly as required by the arrow definition.
- The finite-projective sheaf `F^r` is `M`. Its coefficient complex is precisely
  `(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M`, rather than an
  arbitrary bounded complex. `P` is the existing strict-perfect package for
  this single complex. At degree zero its `N 0`, `i 0`, `p 0`, `splitting 0`
  are the displayed finite-free summand presentation. The remaining terms are
  zero, so their package entries are harmless auxiliary presentations. Every
  displayed splitting of M extends to such a package, using rank zero outside
  degree zero. The helper supplies the canonical bounds [0,0] by Mathlib's
  `HomologicalComplex.isZero_single_obj_X`; there is no additional boundedness
  hypothesis. No projectivity assumption beyond the actual displayed splitting
  is needed or imposed.
- `P'` ranges over every second presentation, including different finite ranks.
- The first conjunct says `.2 ≫ .1 = 𝟙 _`; the second says
  `.1 ≫ .2 = 𝟙 _`. Since `.1` is pi and `.2` is rho, these are both inverse
  equations in Lean's diagrammatic composition order.
- The final conjunct equates the ordered pairs for `P` and `P'`, asserting
  independence of both arrows. The forward arrow is the same intrinsic counit
  mate, and uniqueness of its inverse gives independence of the second arrow.
  The existing total-inverse summand characterization identifies the degree-zero
  specialization with the exact retract formula, not an arbitrary inverse.

Dependency declarations read from current server source (the module is absent
from the older local checkout): `Sheaf.Paper.ProjectionFormulaArrows`, including
`CategoryTheory.derivedProjectionFormulaMate`,
`CategoryTheory.derivedProjectionFormulaRetractInverse`,
`CategoryTheory.tensorAdjunctionTotalInverse_summand`, and
`SheafOfModules.ringedProjectionFormulaArrows`. The package is the existing
`SheafOfModules.StrictPerfectCoefficientPackage` from
`Sheaf.Paper.StrictPerfectCoefficientPackage`, re-exported by that module.
The canonical tensor comparison proof dependency is imported non-publicly as
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback`. The finite-free proof node has
no Lean record yet, so there is no proof import to add for it.

Edge cases checked: M=0, rank N=0 (the empty finite sum), N=1, different ranks
and different splittings, zero E, and zero coefficient rings. No positivity or
nonzero assumption appears. Degree-zero concentration is built by `single`,
not a restriction on an arbitrary coefficient complex. The universal second
package does not require equal ranks, inclusions, or projections.

Searches:

- `msearch.py leanfinder`, query `finite projective summand projection formula
  inverse independent splitting`: eight module/projection hits, including
  `Module.Projective.out`; none is this derived ringed-topos statement.
- `msearch.py loogle`, query `CategoryTheory.Adjunction, "tensor"`: ten monoidal
  adjunction, tensor-hom, or module embedding hits; no summand inverse statement.
- `msearch.py grep`, query `projectionFormula|projection_formula` in
  `CategoryTheory`: zero Mathlib hits.
- `msearch.py leansearch`, query `finite projective summand projection formula
  inverse independent presentation`: unavailable (Internal Server Error).
- `rg` in the upstream WeilConjectures sources and `lean/Sheaf` for projection
  formula names: unrelated six-functor package projection isomorphisms upstream;
  no exact statement or duplicate declaration. Item-id search likewise had no
  matching upstream declaration. Exact proposed declaration-name searches in
  Mathlib, upstream and the project's Lean sources returned no hits.

No statement correction, disputed statement, new node, or dependency repair.
The module preserves the node's statement verbatim in its natural-language record.

## Validation

Resumed after the human authorized the local side-project overlay through
`scompile.py`. The earlier server-only concern is superseded by that instruction.
`scompile.py NU lemma-weil-pbc-projection-formula-projective-summand` passed
with no diagnostics: sandbox check 26.5 seconds, library-module check 32.4 seconds.
Delivery preflight is run with `deliver2.py NU
lemma-weil-pbc-projection-formula-projective-summand --no-push`; no push or second-reading
claim is made by this worker.

## Second reading by NU

Read independently against the item JSON, its only statement dependency
`def-weil-pbc-projection-formula-arrows`, that dependency's current published
source (`scompile.py --source Sheaf.Paper.ProjectionFormulaArrows`), the actual
`StrictPerfectCoefficientPackage` structure, and the canonical tensor-comparison
interface. Read the blueprint item and detailed `proper_base_change.tex`, lines
5373–5471 (definitions 1263–1264 and lemmas 1265–1266). This source is the blueprint,
not a Stacks lemma with additional standing scheme hypotheses. The Stacks-sourced
comparison is used through the published dependency, not redefined here.

Object/hypothesis/conclusion checklist and verdicts:

1. Ringed topoi h, coefficient rings R,S, and their ring map: `C,D,JC,JD,R,S,RI`,
   `uInv,uPush,adj`, finite-limit preservation, `I,c`. These are exactly the
   small-site ringed-topos parameters in definition 1264; PASS.
2. Ordinary module pullback and direct image: `uStar,hobj,hmap,V,am` and the
   additive instances identify scalar extension of inverse image and its right
   adjoint. This uses the recorded declaration, not a similarly named scheme
   pullback or a private tensor construction; PASS.
3. Unbounded derived operations and their canonical comparisons:
   `HasDerivedCategory`, `LF,epsilon,hLF`, `PR,PS,hPR,hPS`, `TR,TS,rR,rS`, `k`,
   `RF,eta,hRF,computeR,computeL,adjD,canonicalAdj`. All are passed unchanged to
   `ringedProjectionFormulaArrows`. The structure `CanonicalRingedTensorComparison`
   includes the scalar-extension insertion and generalized pure-tensor equation;
   the derived comparison is uniquely specified on K-flat representatives.
   `canonicalAdj` fixes the counit against the ordinary adjunction. These encode
   the dependency's operations, not extra properness or exactness assumptions;
   PASS.
4. Arbitrary E in D(S): `E`, with `K,hK,repE` its chosen K-injective
   representative, exactly as in the arrow definition; no boundedness on E; PASS.
5. Finite projective coefficient sheaf F^r and displayed splitting: `M` and
   `P : StrictPerfectCoefficientPackage _ ((HomologicalComplex.single _ _ 0).obj M)`.
   Opened the structure: `N 0 : ℕ`, `i 0`, `p 0`, `splitting 0 : i 0 ≫ p 0 = 1`
   are precisely a finite-free retract. Degree zero of single is canonically M;
   other terms are zero. Any displayed splitting extends by zero-rank splittings
   in the other degrees, so the package imposes no extra projectivity condition
   or chain-map constraint. The helper constructs bounds [0,0] using the existing
   zero-term lemma; no boundedness assumption is added; PASS.
6. The specified arrows pi and rho: `ringedProjectionFormulaSummandArrows` is
   exactly the published pair specialized to this single complex and bounds.
   Opened the dependency's body: pi is `derivedProjectionFormulaMate` (the
   upstream adjoint projection map), and rho is `Q.map s` transported through
   canonical mixed-tensor and derived-pushforward representatives. Opened
   `tensorAdjunctionTotalInverse_summand`: its equation identifies each summand
   with `tensorAdjunctionRetractInverse`, whose body is precisely image of i,
   free inverse, then tensor with p. Thus degree zero gives the node's rho,
   rather than an arbitrary inverse; PASS.
7. Both inverse equations: first conjunct `.2 ≫ .1 = 𝟙 _` is rho followed by pi;
   second `.1 ≫ .2 = 𝟙 _` is pi followed by rho. Lean uses diagrammatic order,
   so these are exactly both equations, merely listed in reverse order; PASS.
8. Independence of both arrows: `P'` is an unrestricted second package for the
   same M and equality of the ordered pairs is the final conjunct. Its ranks,
   inclusions and projections need not equal P's. Universal P,P' also includes
   P'=P, so the inverse claims are not conditional on a distinct presentation;
   PASS.

Edge cases: Fin 0 and the zero coefficient sheaf are allowed, including the
empty finite product; no positive rank is assumed. E=0, the zero ring, all
characteristics, and degenerate/empty sites are admitted. No scheme assumption
is introduced, so the empty scheme is not excluded when its site is used.
Degree zero is literal single-complex placement of a sheaf, not an excluded
cohomological degree. The site/object/coefficient universe u and derived
universe w are exactly those of the small-site dependency and are explicitly
bound. There is no extra universe equality beyond its established size
convention. No independent index universe is involved.

Independent H4 searches used different queries from the worker:

- LeanFinder: `inverse of projection formula for retract of a finite direct sum`:
  eight direct-sum/decomposition results, none this statement.
- Loogle: `CategoryTheory.Adjunction, "inverse"`: ten results concerning
  localizations and adjunctions, none the displayed summand equations.
- LeanSearch: `projection formula inverse independent of finite free splitting`:
  unavailable (Internal Server Error), recorded by msearch without a verdict.
- rg over Mathlib/CategoryTheory, upstream WeilConjectures, and project lean/Sheaf
  for `projectionFormula|projection_formula|ProjectionFormula|rightAdjointProjection`,
  and exact declaration names plus `projective.summand` over all Mathlib:
  no duplicate. Opened upstream `Adjunction.rightAdjointProjectionMap` and
  `Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable`.
  The former is the canonical forward mate already reused by the dependency;
  the latter is a scheme-etale/dualizable isomorphism statement, not this
  arbitrary ringed-topos result with its specified retract inverse and
  presentation independence. Neither replaces this node.

No mismatch found and no Lean or node changes required. No new nodes or
additional dependency modules are present. The helper has real data and uses
an existing Mathlib proof only for its bound; the sole theorem proof is `sorry`.
Its source/blueprint docstring gives all three proof steps: adjoint naturality,
the two splitting calculations with the finite-free result, then inverse
uniqueness. Imports retain the stated canonical-comparison proof dependency;
the finite-free proof node has no recorded module to import. No file-local
notation, private definitions, hidden let/show in the statement, or unbound
variables were found. The normalized recorded lean.statement agrees with the
file signature. The second reading adds only this review and validation record.

Second-reader validation: the required scompile.py command with the absolute
module path passed cleanly, sandbox check 26.1 s and library-module check 32.3 s,
with no diagnostics. All delivered Lean files (one) were compiled.
