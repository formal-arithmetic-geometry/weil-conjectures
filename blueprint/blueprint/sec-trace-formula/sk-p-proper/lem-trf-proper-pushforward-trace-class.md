+++
id = "lem-trf-proper-pushforward-trace-class"
kind = "remark"
title = "Proper pushforward compatibility of trace maps: discharged"
order = 2333
uses = ["def-trf-borel-moore-pushforward", "def-trf-coefficient-pushforward", "thm-trf-trace-proper-compatibility"]
+++
Let $p:C'\to C$ be proper, $c_i'=c_i p$, and let
$u':Lc_2'^*K\to Rc_1'^!K$ be a correspondence on $C'$. Then
$(\operatorname{id}_X,p):(C',c')\to(C,c)$ is a proper pushforward diagram
in the sense of [def-trf-coefficient-pushforward], with pushforward
correspondence $p_!u':=[\operatorname{id}_X,p]_!u'$, and the induced map of
fixed schemes is the proper base change $p_F:F'\to F$ of
[lem-trf-fixed-map-proper]. The compatibility

$$
\operatorname{Tr}_c(p_!u')=(p_F)_*\operatorname{Tr}_{c'}(u')
$$

(with $(p_F)_*$ the pushforward of Borel–Moore sections along the
proper $p_F$ of [def-trf-borel-moore-pushforward], sometimes written
$(p_F)_!$) is therefore the special case $f=\operatorname{id}_X$, $g=p$ of
[thm-trf-trace-proper-compatibility] (Varshavsky,
[loc. cit.](https://arxiv.org/abs/math/0505564), 1.2.5); neither a
properness hypothesis over $s$ nor a Cartesian condition is needed. The
former open interface is therefore retired and is no longer listed among
the unresolved inputs of this chapter.
