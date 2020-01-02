def setupRust() {
    sh "rustup component add rustfmt clippy"
    sh "rustup install nightly"
    sh "cargo update"
    sh "cargo"
}

pipeline {
    agent none

    stages {
        stage('Builds') {
            parallel {
                stage('Quick') {
                    agent {
                        docker {
                            image 'coqorg/coq:8.10.2'
                        }
                    }
                    steps {
                        sh "git submodule update --init"
                        sh "eval `opam config env`; make -j"
                    }
                }
                stage('Full') {
                    agent {
                        docker {
                            image 'coqorg/coq:8.10.2'
                        }
                    }
                    steps {
                        sh "git submodule update --init"
                        sh "eval `opam config env`; ./build.sh"
                    }
                }
            }
        }
    }
}
