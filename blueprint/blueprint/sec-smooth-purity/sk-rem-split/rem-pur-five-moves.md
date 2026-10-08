+++
id = "rem-pur-five-moves"
kind = "remark"
title = "The five moves of the purity proof"
order = 2038
+++
The five moves are the whole proof. Conveniently located: the
rank-one computation (Kummer $c_1$, excision, Gysin identification of
$Rs^{!}(1)[2]$ with $H^2_s$) — inside [thm-pur-kummer-affine-line], proved from
the Kummer sequence and the cohomological-dimension bound of §[sec-curve-estimates], with the
orientation itself derived in [lem-pur-gysin-structure]; the Künneth and
frame-independence arguments (the Thom class is the $\Aaf^1$-class written in
coordinates) — inside [cor-pur-affine-space-purity]; the geometry of the deformation of a
*section* — [lem-pur-dnc-section-geometry], used by [thm-pur-dnc-invariance] and through it
by [thm-pur-finite-coefficient-smooth-purity]. Purity for regular closed immersions
([thm-pur-regular-immersion-purity]) is *not* one of the moves: it is a consequence of
[thm-pur-finite-coefficient-smooth-purity] for the two structure morphisms together with the
co-projection [lem-pur-coprojection], and the deformation to the normal cone
is never applied to a general regular immersion. The formal six-functor
bookkeeping (base change, transpose composition, cup products, coefficient
transport, Frobenius equivariance, the trace normalization for the Lefschetz
formula) is all downstream of [thm-pur-finite-coefficient-smooth-purity] and absent here.
