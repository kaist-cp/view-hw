From coqorg/coq

COPY --chown=coq:coq . view-hw

USER coq
WORKDIR view-hw

RUN git submodule update --init
RUN make -j
