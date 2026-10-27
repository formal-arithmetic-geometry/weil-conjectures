# Stage-1 delivery: lem-sfb-local-ddbar-potential-calculus

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-ddbar-potential-calculus.json: item, split into seven explicit coordinate-calculus steps, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-real-smooth-differentiation.json: statement, Mathlib leaf for smooth real differential rules and the positive-real logarithm.
- dag/nodes/sec-six-functors-basics/lem-sfb-real-second-derivative-symmetry.json: statement, Mathlib leaf ContDiffAt.isSymmSndFDerivAt, FDeriv/Symmetric.lean:533.
- dag/nodes/sec-six-functors-basics/lem-sfb-analytic-real-smooth.json: statement, Mathlib leaf for analytic smoothness, scalar restriction and identification of the real differential.
- citations.json contains a verbatim statement quote for every step/node pair. searches.jsonl records all searches made in this attempt.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, ddbar, pluriharmonic, Wirtinger, Dolbeault and complex-Hessian terminology found no declaration of this result. The analytic hits concern Euler products and weights, not these differential forms.

## Literature wanted

WANTED: a local copy of Demailly, Complex Analytic and Differential Geometry, I §3.C, printed pp.23–25, for this item. The item already names the author PDF https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf. I read those pages online by streaming the PDF through pdftotext to stdout; no literature file was downloaded into the project or sandbox. The web PDF reader timed out, but the streamed author source succeeded. Equations (3.13)–(3.19) give the precise Wirtinger and form conventions, their identities, and holomorphic pullback. The additional log-modulus argument is the explicit agent calculation below, not a claim that Demailly states our whole packaged lemma verbatim. proof_origin.by is agent.

## Corrections and route

There is no statement dispute. I retained the statement, real normalization i/(2 pi), open domains, arbitrary nonnegative dimensions, and power-series meaning of holomorphic.

The unsplit item had no proof. It now contains the arguments for each clause instead of replacing those clauses by newly named nodes. The three new statements are lower-level calculus tools, each already in Mathlib; none refers to D_U, forms of type (1,1), holomorphic pullback of the Hessian, or log-modulus pluriharmonicity.

I read SETUP's three levels, GOAL, the chapter and unit records, and the current latest blueprint unit and direct-images proof (3). The inherited supporting route is through projective analytic geometry/GAGA in the Kodaira chain. The current unit text itself has no ddbar lemma. The recorded ancestor is null (blueprint_refs.py ancestor confirms this), and its inherited via chain is preserved, extended by the item for each new leaf. No unit or chapter is changed.

## Not duplicates

The whole DAG and current blueprint were searched for Wirtinger, pluriharmonic, Schwarz/Clairaut, mixed partials, second derivative, real smoothness, real differentiation, and the exact Mathlib declarations. blueprint_refs searches for Wirtinger, Cauchy, Schwarz, real differentiation, smooth calculus, second derivative and holomorphic pullback found no relevant imported node. The broad analytic and holomorphic searches returned weight/series nodes rather than the present calculus statements.

lem-sfb-real-smooth-differentiation vs lem-sfb-complex-analytic-derivative-rules: the existing node assumes complex analyticity or complex differentials; it does not provide real smooth closure and differentiation for an arbitrary smooth nonholomorphic potential or the real logarithm.

lem-sfb-analytic-real-smooth vs lem-sfb-analytic-germ-differentiable: the existing node is one-variable complex differentiability at a point; it does not assert real smoothness or equality of real and complex differentials in arbitrary finite dimension.

lem-sfb-analytic-real-smooth vs lem-sfb-complex-analytic-derivative-rules: the latter gives complex derivative analyticity and complex differential algebraic rules, not restriction of those derivatives to real scalars.

lem-sfb-real-second-derivative-symmetry vs lem-sfb-real-smooth-differentiation: the first is the C2 Schwarz theorem, with its own exact Mathlib match; the second is a collection of closure and first-differential rules and does not assert symmetry.

No Stacks tags occur in the new nodes, so there are no pairs sharing a Stacks tag. These are real/complex analysis results, with exact Mathlib source citations rather than invented Stacks references.

## Review by NZ

I checked the mathematics against Demailly I §3.C (3.13)–(3.19), printed pages 23–25, and against the actual Mathlib source signatures listed in each new node. Demailly uses the same 1/2 Wirtinger derivatives, exterior multiplication on the left, and complex-valued forms on real tangent vectors. Thus our displayed Hessian formula has the intended order and sign.

For the new real calculus leaf I read ContDiff/Basic.lean:103–115,154–166, ContDiff/Operations.lean:180–188,445–455, ContDiff/Comp.lean:218–228,715–734, ContDiff/Defs.lean:998–1003, FDeriv/Add.lean:208, FDeriv/Mul.lean:205, FDeriv/Comp.lean:105, FDeriv/Const.lean:114, FDeriv/Linear.lean:57, and Log/Deriv.lean:47–80. Each clause specializes directly over R; complex scalar targets in the product rule are real normed algebras. Smooth differential maps follow with m=n=infinity. The logarithm hypotheses are satisfied by positivity, not by claiming smoothness at zero.

For the symmetry leaf I read Symmetric.lean:88–101,530–545. Over R the minSmoothness bound is 2, and the conclusion is precisely symmetry evaluated on arbitrary tangent vectors. This applies on our open sets and to each smooth coefficient, so no boundary differentiability assumption is hidden. For the analytic-real leaf I read Defs.lean:718–727, Operations.lean:1020–1056, FDeriv/Analytic.lean:110–130 and FDeriv/RestrictScalars.lean:40–65. Open sets supply unique differentiability; the fields form the standard R/C scalar tower. Finite complex coordinate spaces are complete, although the chosen open-set analytic smoothness theorem does not require that assumption. The analytic convention is locally convergent series on both sides.

Step 1 uses the real calculus leaf for smooth coordinate derivatives, composition with evaluation and conjugation, and differential linearity. Its symmetry citation gives exactly the commutation of real directional derivatives, which extends by the displayed constant linear combinations to Wirtinger derivatives. These are not consequences of a definition-only node.

Step 2 uses that calculus statement for smoothness and real-linearity; the other calculation is in step 1. I checked that conjugating i gives a minus sign and reversing dbar z_r wedge dz_s cancels it. The Hermitian symmetry Hbar_rs=H_sr is sufficient, with no positivity assumption.

Step 3 uses the same calculus leaf for smoothness of first derivative coefficients and the Schwarz leaf for commutation. I checked each third-derivative symmetry on a smooth first-derivative function. For the barred sum, swapping k and s reverses the three-form sign; diagonal repeated factors vanish. Thus no unproved general d-squared theorem or Dolbeault identity is silently invoked.

Step 4 reads the statement of lem-sfb-complex-analytic-derivative-rules for analyticity of the complex differential and lem-sfb-complex-analytic-function-operations for linear maps, composition and finite tuples. The analytic-real leaf supplies real smoothness and complex-linearity of the real differential. The displayed identities g_y=i g_x and dbar g=0 follow immediately. The existing statements really give analytic derivative coefficients, not merely differentiability at a point.

Step 5 uses the real calculus leaf's chain and product rules, together with the coordinate results already proved in step 4. The explicit formula has F_{r,a} and conjugate F_{s,b} in the correct positions. The possible extra derivative of conjugate F_{s,b} is zero because F_{s,b} is holomorphic, already proved in step 4. I checked that tangent-vector pullback gives exactly the same coefficients. This avoids citing a general real pullback theorem as if it asserted type-split naturality.

Step 6 uses the analytic-real leaf for smooth h and the real calculus leaf for real/imaginary projections, products, composition and log differentiation. Nonvanishing makes q=|h|^2 positive at every point. The real derivative of squared modulus is written out before taking its Wirtinger component; the quotient simplification uses h nonzero.

Step 7 reads both existing analytic leaves: the derivative leaf makes h_z holomorphic and the operations leaf explicitly includes reciprocal at a nonzero value and multiplication. Hence the quotient is holomorphic. The Schwarz leaf commutes the derivatives of the smooth log q from step 6; it does not infer zero mixed Hessian from a one-variable harmonicity lemma. All step citations are copied verbatim into citations.json.

I tested zero-dimensional source and target, empty domains, constant potentials, phi=|z|^2 in one variable (giving dx wedge dy/pi), constant nonzero h, h=exp(z), and h=z on C minus {0}. The last example has no global holomorphic logarithm, yet h_z/h is holomorphic and the proof works. A zero of h would invalidate log smoothness, and an antiholomorphic coordinate change would invalidate the chain-rule simplification; neither is allowed by the statement. The new C2 symmetry leaf does not assert commutation for merely existing second partial derivatives. Each proof step is shorter than 1100 characters, so no long step conceals a further lemma.

I checked delivery-errors B–E: new leaves have self-contained statements, no proofs, precise declaration/file/line matches, actual logged searches, and filled blueprint fields; cited statements supply the facts used; no new node restates an item clause; no stronger hypotheses or weaker conclusions are introduced.

## Unfinished work

No mathematical part is left unfinished. This is a stage-1 delivery only: no Lean was written and no compiler, Lake or build tool was run. The required remote preflight remains the delivery check.
