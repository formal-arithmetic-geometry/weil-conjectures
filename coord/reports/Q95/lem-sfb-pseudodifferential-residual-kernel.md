# Q95: lem-sfb-pseudodifferential-residual-kernel

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pseudodifferential-residual-kernel.json — item statement, unchanged; status split, five proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-negative-symbol-finite-kernel.json — new statement-only node, unsplit; no exact Mathlib match.
- citations.json — one verbatim statement quote for each of the fifteen step citations.
- searches.jsonl — actual msearch outputs; inherited item searches are retained.

One new node, zero new Mathlib leaves. No Lean, compiler, Lake, repository edits or direct git commands.

## Attachments

None. Searched lean/WeilConjectures for the item id, pseudodifferential, residual-kernel, smoothing operator and negative-symbol kernel terminology. No project declaration states the item. The existing upstream sorry declarations are not used as finished proofs.

## WANTED

WANTED: Demailly, Hodge Theory and Complex Algebraic Geometry, Part I §3.B, printed pp.12–14, for lem-sfb-pseudodifferential-residual-kernel (inherited source literature/demailly-hodge-ams.pdf). Two attempts to read the inherited online PDF timed out; it is not present under literature/.

WANTED: Demailly, Differential and pseudodifferential operators on manifolds, §3, (3.3)–(3.5), (3.8)–(3.9), and (3.12)–(3.13), printed pp.6–10, for lem-sfb-negative-symbol-finite-kernel and the item. Read the online course at https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf using the web reader. No download or literature edit was made. The course uses exp(2πi x·ξ); our formulas use exp(i x·ξ)/(2π)^m, consistently with the live definition. The source explicitly treats the local kernel, finite cutoff globalization, and rapidly decreasing symbols. The finite differentiability and representation-independence argument here is written by the worker, so proof_origin remains agent.

## Audit of the imported item and route

The item was unsplit and the sandbox initially contained no node/report/searches. There is no repair note. The item and statement dependencies are unchanged. The unused ambient bundle G is retained as imported; the proof does not require a metric on E or F or equal bundle ranks.

I read GOAL.md, the stage-1 brief and contract, SETUP.md's three blueprint levels, the worker role, delivery-errors B–E whole, the recorded unit/chapter, and the current latest chapter and unit text. The latest blueprint puts sk-thm-sf-ctf-stability under sec-six-functors-basics and its direct-image proof (3) is the inherited higher-level route. This is a local analytic prerequisite already below that route, not a replacement for a unit step. blueprint_refs ancestor returns None on the live ancestry; I retained that null node, its place and via list. The new node prepends this item to via. No unit realized fields are changed because this item is not the unit's key node.

There are two potential false shortcuts, neither used: membership in each Ψ^{-L} does not by definition provide a single symbol in their intersection, and agreement on smooth sections alone does not by itself identify arbitrary maps on distributions. The five steps supply kernel uniqueness across different representations and equality of test transposes respectively.

## New-node argument for the next worker

lem-sfb-negative-symbol-finite-kernel is a local finite-order integration lemma, not a renamed residual-operator assertion. On a compact set in the x chart, each mixed derivative of exp(i(x-y)·ξ)a(x,ξ), of total order at most k, is a finite sum of polynomial factors in ξ of degree at most k times x derivatives of a. Its norm is at most C(1+|ξ|)^{r+k}, integrable since r+k<-m (polar radial exponent r+k+m-1<-1). Terms in which derivatives hit χ or ψ obey the same bound on fixed compact supports. Dominated differentiation gives joint C^k regularity and the derivative formulas, including locally uniform tails for the frequency cutoff. Spatial compact supports allow extension by zero across the chart boundary. For compactly supported smooth inputs, the absolute bound times their L1 norm justifies exchanging y and ξ integration, gives the cutoff limit and derivative formulas. This proves the claimed local action identity. The new node itself has no proof, proof sketch, proof dependencies or proof_origin; this argument is recorded only here for its future worker.

Read Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:497–529: VectorFourier.contDiff_fourierIntegral at 507 is about a fixed frequency function and derivatives in its Fourier argument. It does not include the x-dependent amplitude, joint x,y derivatives, compact spatial cutoffs or the oscillatory action identity. The node therefore needs a parameter-dependent integration argument and is not a one-line specialization of that declaration. Two semantic phrasings, LeanSearch, Loogle and directory grep are recorded exactly as run. Other hits were integration on Schwartz space, fixed Fourier transforms and convolution regularity; no exact match. The item also received fresh logged semantic, Loogle, grep and LeanSearch searches with a second phrasing. The wrapper's single-file grep loses the filename (it prints lines as files), and one speculative ParametricIntegral path does not exist: these were not relied on as absence evidence or recorded in any node. The successful Analysis/ and Analysis/Fourier/ directory searches are the relevant evidence; the full log retains all invocations.

## Not duplicates

lem-sfb-negative-symbol-finite-kernel vs lem-sfb-pseudodifferential-residual-kernel: finite-order local Euclidean symbol input with an explicit frequency integral and C^k bound, versus an arbitrary global operator lying separately in every negative-order class with a smooth kernel on all distributions. The item proves the assembly, compatibility and distributional identification.

lem-sfb-negative-symbol-finite-kernel vs lem-sfb-compact-symbol-frequency-kernel: the latter Fourier-transforms the symbol in the position variable, proves decay in that dual variable and describes the Fourier transform of the output on Schwartz inputs; it does not give finite joint regularity of the physical-space x,y kernel from sufficiently negative frequency order. I opened both statements.

lem-sfb-negative-symbol-finite-kernel vs lem-sfb-fourier-moment-representative: the latter takes an L2 function with a fixed frequency representative and produces its C^r representative; it has no position-dependent matrix amplitude or joint kernel claim.

lem-sfb-negative-symbol-finite-kernel vs lem-sfb-schur-l2-matrix-kernel: the latter proves an L2 boundedness criterion for a measurable kernel from two integral norm bounds, not its differentiability or identification with symbol quantization.

Whole-DAG searches used kernel/symbol, negative-order, smooth kernel, Fourier, test-function separation, strong dual and density keywords. Whole-blueprint searches used smooth kernel, distribution, pseudodifferential, Fourier, test function, symbol, quantization, negative symbol, finite kernel and compactly supported kernel. Analytic statements were absent; Fourier–Deligne nodes concern different algebraic objects. Existing scalar separation/local-integrability/pointwise leaves are reused. No Stacks tag is appropriate to this real-analysis statement; source places are Demailly's actual numbered formulas, with no SGA reference.

## Review by Q95

I re-read delivery-errors B–E against the actual JSON statements, not just dependency ids. The new lemma introduces U, m, p, q, k, r, a, χ, ψ, H, the cutoff and the input f, and cites the existing symbol convention and scalar-field notion. It carries a statement only and all its recorded searches ran. The item proof steps are 1102, 851, 886, 310 and 1098 characters; no long step exceeds 2000 characters or hides an uncited representation-comparison theorem.

Step 1 uses exactly the live definition's finite representation by localized symbols plus a smooth remainder, including the real part and both cutoffs. The new lemma says precisely that these local terms have C^k kernels and the correct action on smooth inputs. I verified r=-(m+k+1)<-m-k, compact supports inside the chart, and that multiplication by γ_i(y)^{-1} converts coordinate dy to the fixed dV. It changes neither bundle rank nor operator direction. Compactly supported local Hom sections extend by zero and their finite sum is a section globally; no patchwise equality is presumed.

Step 2 uses the existing scalar lemmas lem-sfb-continuous-local-integrability, lem-sfb-smooth-test-ae-separation and lem-sfb-continuous-ae-pointwise. I opened all three statements: they respectively give local integrability for a continuous coefficient on an open subset of R^m, almost-everywhere vanishing from all real smooth compactly supported test integrals, and pointwise equality of continuous almost-everywhere equal functions. Real coefficients are regarded in C and extended arbitrarily by zero outside the chart; continuity is needed only on the chart. The cited test-distribution definition supplies exactly the smooth embedding and dual-density convention. No node merely defining distributions is used for a density theorem.

Step 3 applies those same scalar statements twice only through their written conclusions. First the difference of the continuous outputs vanishes as a distribution, so step 2 makes the outputs pointwise equal. Then fixing each output point and functional reduces kernel uniqueness to arbitrary scalar input tests in a single chart. I checked the factor γ>0 and that a section supported compactly within the chart extends smoothly by zero. All matrix entries vanish; no Schwartz kernel theorem or separability of a tensor-product test space is assumed.

Step 4 is elementary: pointwise equality identifies K_0 with a C^k section for every finite k, so the one resulting section is smooth by the definition of C-infinity. It introduces no new analytic estimate or limiting kernel.

Step 5 uses the exact transpose convention of the live symbol/operator definition, which includes both spatial cutoffs, and the test-space definition's evaluation formula. The transpose of each localized term maps smooth tests to smooth tests as required for the defined distributional action; the smooth-kernel action is defined with the same duality. Equality on all smooth sections annihilates the smooth dual-density difference Bφ-C_Kφ. The three scalar leaves separate its coefficients as in step 2. Equality of the actual test sections then implies equality after evaluation by every continuous functional u. I checked the direction B:T(F)→T(E), no conjugation in real duality, the x integration and final density dV(y), and that no illegitimate evaluation of a distribution on a finitely differentiable function occurs. In particular the C^k kernels are used only on smooth inputs until K is known smooth.

Small cases: zero ranks give zero-sized matrices and zero sections; empty N gives the zero kernel; the zero operator and a smooth finite-rank integral operator are included by the empty-sum convention. On a circle a Fourier multiplier with decay only |n|^{-s} has a finite kernel regularity threshold and cannot be smuggled into the all-negative-orders hypothesis. The strict inequality r<-m-k avoids the logarithmically divergent borderline radial integral. Different order representations yield one kernel by the pointwise uniqueness argument. Distributions such as a Dirac mass or its derivatives are covered by the last transpose identity without a Sobolev hypothesis. No statement dispute or correction was necessary.

Every uses entry has its verbatim statement in citations.json. The off-unit scalar leaves are actually in this same unit, and no generic off-route theorem is introduced. I corrected the initial temptation to use a strong-dual density assertion by giving the explicit test-transpose comparison. I also avoided duplicating the already existing scalar test-separation and Fourier-moment nodes. Nothing remains unfinished in the item's split; the new local lemma is intentionally an unsplit next-stage-1 item.

## Validation

Required remote dry run and final delivery recorded by deliver.py; see its retained output for the concrete commit. Independent maintainer review is still the delivery's mathematical acceptance step.
